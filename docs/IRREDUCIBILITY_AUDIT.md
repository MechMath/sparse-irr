# 稀疏多项式不可约性：论文与 Lean 的对应核查

**版本范围：本页只对应原来的7页 PDF，是历史核对记录。** 18页非独立稿的全部编号定理
和当前前提见 [全篇对应表](PAPER_1021_MAP.md)，第3、4节的后续实现已完成。

核查对象：仓库根目录的 `AI4Math_Irreducibility.pdf`（7 页），以及
`0928_4_problems_progress_notes(1).pdf` 中的定理 8。核查日期：2026-10-19。

## 结论

**新论文的主定理 2 与原笔记定理 8 的四项结论一致，原仓库已全部无条件证明。**
它们分别是：整数单变量稀疏多项式不可约性的 many-one coNP-hardness、可约性的
many-one NP-hardness、不可约性的恰好一次 oracle 查询 NP-hardness，以及多项式时间
不可约性测试推出 `P = NP`。不能把第三项误读成不可约性的 many-one NP-hardness。

新论文使用的 FFK 同时逼近、无进位提升、Eisenstein 和 Ljunggren 证明路线也已经在
`SparseIrred/FFK/` 中实现。因此主结论不依赖 `SSSLargeGap`，也不需要先补完一般的
Sawin–Shusterman–Stoll 定理。

本次增加 `SparseIrred/Irreducibility.lean`，补齐论文表述与原接口之间的转换，并增加引理 5
的严格正余数及唯一性结论、引理 7 的显式输出长度界。全部入口经 `import SparseIrred`
可用。

## 逐项对应

下表中新入口均在命名空间 `SparseIrred.Irreducibility` 下。

| PDF 结论 | 原有证明 | 新入口及补充 |
|---|---|---|
| 定理 2（第 2 页）四项复杂性结论 | `irreducibility_coNPHard`、`reducibility_NPHard`、`irreducibility_NPHard_oneQuery`、`P_eq_NP_of_irreducibility_mem_P` | `irreducibility_hardness` 汇总四项，不增加假设 |
| 引理 3（第 2–3 页）：`S ≠ 0`、`A ∈ ℤ[X]`、`A(0) ≠ 0`、`deg A = 2d`、`A* = A`、有理解域互素性编码可满足性、所有 `M ≥ 0` 的单位根等价 | `Construction/Laurent.lean`、`RootsOfUnity.lean`、`Norm.lean` | `satisfiability_encoding` 汇总这些性质；`Apoly` 的类型本身为 `ℤ[X]`，`toLaurent_Apoly` 证明 Laurent 截断没有丢项 |
| 定理 4 的式 (2)（第 3–5 页）：`FF* = KK*` 强制 `K ∈ {±F, ±F*}` | `FFK.ljunggren_gapPoly` | `ljunggren_gapPoly` 使用论文的 `reverse`，接受 `ℚ[X]` 中的互素条件；自动从乘积等式推出 `K(0) ≠ 0` |
| 定理 4：再假设无复单位根，则 `F` 在 `ℤ[X]` 中不可约 | `FFK.irreducible_gapPoly` | `irreducible_gapPoly` 接受论文的有理互素条件；`isRelPrime_of_rational_coprime` 证明整数多项式中的相应条件 |
| 引理 5（第 3–4 页）：`1 ≤ d ≤ 8^s`、`κ = ⌊L/d⌋ > 2m`、每个指数对应唯一整数商，移位余数严格在 `(0, κ/2)` 内 | `FFK.exists_simultaneous_approx`、`FFK.exists_lift_modulus` 原已提供提升所需的条件，但未要求余数严格大于零，也未暴露 `d` | **`exists_shifted_residue_modulus` 补齐完整结论**，保留同样的阈值 |
| 引理 6（第 5 页）：完整的 (PB1)，以及 `p_k ≤ 64(k+1)^2`、`q_i ≤ 64(i+2)^2` | mathlib `Chebyshev.two_pow_le_mul_lcmUpto`、`Machine.two_pow_le_pow_primeCounting`、`Machine.nth_prime_le`、`Machine.oddPrime_le` | `lcm_primeCounting_bounds` 给出 (PB1) 两段不等式，包含 `x = 0`；`prime_index_bounds` 汇总素数界 |
| 引理 7（第 6 页）：确定性多项式时间构造、规范稀疏编码长度为输入长度的多项式、式 (5) 满足 (G1) | `reduce_mem_FP`、`Machine.canonTerms_reducePoly`、`Machine.reduceStr_eq_reduce`、`FFK.FFKThreshold_Mval`；原有详细中间界位于 `Machine/Bounds.lean` | **`polynomial_time_sparse_reduction` 明确给出同一台确定性 TM 及一个自然数系数多项式，同时约束运行时间和输出位长**；主分支输出确为 `encPoly (Hfinal Φ)` |

## 表述差异的处理

1. **倒数多项式。** 论文的 `P*` 是 `P.reverse`；原 FFK 入口使用 mathlib 的
   `P.mirror = P.reverse * X^P.natTrailingDegree`。常数项非零时两者相等。
   新的定理 4 入口证明 `F(0) ≠ 0`，再由 `FF* = KK*` 推出 `K(0) ≠ 0`，没有额外假设。
2. **互素性。** 论文假设 `gcd_{ℚ[X]}(A, X^N-1) = 1`，Lean 使用等价的 `IsCoprime`。
   原 FFK 入口要求 `IsRelPrime` 于 `ℤ[X]`。新转换先排除正次数公因子，再利用
   `X^N-1` 的常数项 `-1` 排除整数非单位公因子。
3. **引理 5 的参数。** 新入口只要求 `L ≥ (10+2m)64^s₀`，在论文中由
   `L = M+N ≥ M` 和 (G1) 得到。它显式写出 `m ≥ 1`；这是论文
   `m = max(N, deg A)`、`N ≥ 1` 已有的条件。
4. **稀疏编码及边界。** `encPoly` 编码非零项，指数递增，系数与指数均为二进制。
   `reduce_correct` 覆盖所有源字符串；非法源编码输出 `X`，退化公式的分支也已证明。
   输出恒为正次数，故这里可约等价于非不可约。零和单位不会被错误地归入可约语言。
   新论文采用 exact-3-CNF，与仓库的源语言相同。

## 验证

复现命令（在仓库根目录运行）：

```sh
lake build
lake env lean scripts/Axioms.lean
lake env lean scripts/DepAudit.lean
git diff --check
```

`scripts/Axioms.lean` 与 `scripts/DepAudit.lean` 已纳入全部新入口。对应输出保存在
`docs/AXIOMS.txt` 与 `docs/DEP_AUDIT.txt`。2026-10-21 更新后的验证结果（包含新增的
上界中间结果及独立素数计数版本的后续补充）：全仓库构建通过（9126 jobs），
202 项定理的公理检查通过，186 个入口的传递闭包包含 72,352 个常量；只达到
`propext`、`Classical.choice`、`Quot.sound` 三个通常使用的公理。
`SparseIrred/` 与根入口未检出 `sorry`、`admit`、公理声明或不安全证明替代，
`git diff --check` 通过。

这里的“主要结论”指上述主定理与全部编号定理、引理。引言中的历史评价、文献综述、
例 1 关于完整因子输出长度的讨论和有限域开放问题，不作为本仓库新增的复杂性定理。
一般的 `SSSLargeGap` 仍只是旧证明路线的显式假设，与新论文结论无关。
