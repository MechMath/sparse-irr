# 第 3 节形式化进度报告（机器实现前快照）

日期：2026-10-22。项目：`SparseIrredHardness`。

**后续更新：用户随后要求形式化实际机器。本页保留为此前的历史快照；下文“当前”、
“尚未构造算法证书”等表述均指机器实现前的状态。最新机器实现、最终定理和验证记录见
[第 3 节完成报告](SECTION3_COMPLETION_2026-10-22.md)。**

新的入口是 `section3_irreducibility_mem_PP_and_PSPACE_of_external_theorems`，
实现证书由 `primeCountingAlgorithmCertificate_of_binaryPrimalityInFP` 构造；
最终前提改为有效素理想计数估计和 AKS 二进制素性判定属于 `FP` 这两项外部文献输入。

**当前结果：第 3 节的内部数学主链已接到实际整数稀疏输入，最终的 `PP`、`PSPACE`
成员资格也已有 Lean 定理。最终复杂性定理显式保留外部计数定理和算法实现证书两类前提；
算法实现证书尚未在本仓库构造。**

本文按用户最新约定报告：引用的外部定理允许作为前提；内部数学定理和推导必须证明；
算法步骤可以不形式化；最终结论必须形式化。因此，“已完成”指下述边界内的数学推导及
条件结论已由 Lean 检查，不表示省略的机器实现也已经验证。

定理名称、代码位置、论文编号与定义逐项见
[定理和 Lean term 对应表](SECTION3_LEAN_MAP.md)。

## 1. 论文版本与目标

本报告同时使用两份本地材料，编号分开标注：

| 材料 | 本次使用范围 | 主结论 |
|---|---|---|
| `1021-AI4Math_Irreducibility.pdf`，18 页 | 原论文第 3 节，PDF 第 7–13 页 | 定理 10：整数稀疏不可约性属于 `PP ⊆ PSPACE` |
| `sparse_irreducibility_complete_qrh.pdf`，8 页 | 独立展开的素数计数证明 | 定理 1.1；引理 3.1、3.2，命题 4.1，引理 5.1及推论 5.2 |

独立稿的引理 3.1 对应原论文的引理 11，不能混用两套编号。根目录 `main.tex`、
`main1.tex` 是较早的困难性稿件，不能作为上述新增第 3 节的编号依据。

本次最终语言是 `SparseIrred.IrredLang`：规范二进制稀疏编码所表示的、在 `ℤ[X]` 中
不可约的多项式。整数常数按环论不可约性处理：正、负素数常数接受，零和单位拒绝；
正次数但非本原的多项式拒绝。格式错误或非规范的字符串不属于该语言。

## 2. 完成情况

| 证明环节 | 当前状态 | 说明 |
|---|---|---|
| 输入、本原性及常数边界 | 已证明 | 包含零、单位、带符号素数常数、非本原多项式；原始项表允许重复指数和相消。 |
| 模素数根与重复根统计量 | 已证明 | `ν+μ` 检测重复因子，证明 `ρ=1` 等价于不可约；无平方自由输入假设。 |
| 引理 11／独立引理 3.1 | 已证明 | 真实因子的 Mahler 界、非首一整正规化、数域判别式预算及异常素数基数界。 |
| 引理 12／独立引理 3.2 | 已证明 | 对实际因子数域证明好素数处根数与次数一素理想的对应。 |
| 命题 13／独立命题 4.1 | 已证明内部推导 | 从外部统一计数估计推出真实多项式的全局平均误差；内部判别式和异常素数界已接入。 |
| 引理 14／独立引理 5.1 | 已证明 | 显式截断、素数计数下界、四分之一误差，以及原始输入长度下的线性位长界。 |
| 推论 15／独立推论 5.2 | 已证明 | 在实际截断上，不可约当且仅当 `2A < 3P`；并接回全部输入边界。 |
| 多数见证与数学接受概率 | 已证明 | 真实见证满足 `#R⁺=P`、`#R⁻=A`，严格多数恰好对应判据；错误编码拒绝。 |
| 定理 10／独立定理 1.1 的最终成员资格 | 已证明条件定理 | 结论使用 complexitylib 的实际 `PP`、`PSPACE` 定义，前提见本报告的外部前提说明。 |
| 外部解析定理本身 | 按约定作为前提 | 不要求接入其他 GitHub 仓库或在本项目重证。 |
| 概率机的构造及多项式运行时间验证 | 按约定省略 | 明确记录为算法实现证书，没有声称证书已经构造。 |

## 3. 两个主入口

### 3.1 统一算术结论

[Section3Arithmetic.lean:37](../SparseIrred/UpperBounds/Section3Arithmetic.lean#L37)
中的完整名称为：

```lean
SparseIrred.UpperBounds.section3_uniform_arithmetic_conclusion
```

它只接收外部有效素理想估计的存在性，先选一个统一整数 `C₀ ≥ 1`，再对**所有**
原始项表 `l : SparseDiv.Appendix.ITerms` 证明：

1. `Irreducible (toPolyZ l)` 等价于包含常数和本原性分支的素数计数测试。
2. 同一个不可约性条件等价于真实有限见证的严格多数测试。
3. 若 `L = (encITerms l).length`，多数见证的选择位数满足
   `2m+5 ≤ 256*(38+Nat.clog 2 C₀)+1536*L+5`。

这里 `m = inputCutoffExponent C₀ (toPolyZ l)`，`X = 2^m`。`C₀` 在输入之前选定，
没有对不同输入另选常数。该定理不需要算法实现证书。

### 3.2 最终复杂性结论

[Section3Conclusion.lean:159](../SparseIrred/UpperBounds/Section3Conclusion.lean#L159)
中的完整名称为：

```lean
SparseIrred.UpperBounds.section3_irreducibility_mem_PP_and_PSPACE
```

下列代码直接调用该定理，展示其精确的前提和结论：

```lean
import SparseIrred.UpperBounds.PrimeCounting

open SparseIrred SparseIrred.UpperBounds

example
    (hExternal : ∃ C : ℝ, 0 < C ∧ EffectivePrimeIdealEstimate (1 / 32) C)
    (hAlgorithm : ∀ C₀ : ℕ, 1 ≤ C₀ → PrimeCountingAlgorithmCertificate C₀) :
    IrredLang ∈ Complexity.PP ∧ IrredLang ∈ Complexity.PSPACE :=
  section3_irreducibility_mem_PP_and_PSPACE hExternal hAlgorithm
```

证明先由统一外部估计选 `C₀`，使用算法证书提供的机器，凭已证明的接受概率阈值正确性
得到 `PP` 成员资格，再使用 complexitylib 已证明的 `PP_subset_PSPACE` 推出 `PSPACE`。

另有固定常数入口
`irreducibility_mem_PP_and_PSPACE_of_primeCounting_certificate`，仅要求该 `C₀` 的估计和
实现证书；上面的统一入口用 `∀ C₀ ≥ 1` 提供证书，再实例化到选出的常数。

## 4. 前提边界

### 4.1 外部文献前提

`EffectivePrimeIdealEstimate δ C` 定义外部有效计数定理的结论。对所有数域 `K` 和
整数截断 `X>2`，它要求

\[
|\pi_K(X)-\operatorname{Li}(X)|
\le C X^{1-\delta}
\bigl(\delta^{-1}\log |D_K|+[K:\mathbb Q]\log X\bigr).
\]

计数对象、数域判别式和对数积分都使用实际数学定义；
`Li(X)` 是 `∫ t in 2..X, 1 / Real.log t`。最终外部参数为
`∃ C : ℝ, 0 < C ∧ EffectivePrimeIdealEstimate (1 / 32) C`。

本仓库将 `δ=1/32` 时的外部计数前提作数值化简，并证明统一整数常数的选择及到 `K=ℚ` 的特化。
本仓库没有另行证明“零点自由定理推出有效计数定理”的解析链，而是接收引用结果在该
间隙下给出的计数结论。这符合允许引用外部定理的约定。

这个单一 Lean 前提汇总了论文中的两项外部解析结果，具体来源如下：

| 外部结果 | 原论文的引用及位置 | 独立稿的引用及位置 |
|---|---|---|
| Cureton–Thorner，*A quasi-Riemann hypothesis for Dedekind zeta functions*，2026，Hexagon `2610.00200v2`，定理 1.1（版本 2）：所有数域的 `ζ_K(s)` 在 `Re(s)>31/32`、`s≠1` 无零点 | **[6]**，§3.1，式 **(22)**，PDF 第 8 页 | **[1]**，§1.1，式 **(2)**，第 2 页 |
| Frei–Sofos–Widmer，*Some applications of the quasi-Riemann hypothesis to class groups and small generators of number fields*，2026，arXiv `2610.18491v2`，定理 1.1：在固定零点自由间隙下的统一有效 Chebotarev 计数界 | **[9]**，§3.1，式 **(23)**，PDF 第 8 页 | **[3]**，§1.2，式 **(3)**，第 2 页 |

第二项按论文取恒等扩张 `K/K` 和唯一共轭类，得到全部非零素理想计数界；再用第一项
提供 `δ=1/32`。当前 Lean 接收这个合并后的计数结论，并未分别建立两项解析结果及其
解析应用的证明。固定间隙的数值化简、提升为统一整数常数，以及 `K=ℚ` 的特化则已证明。

原论文 **[2]**／独立稿 **[2]** 的
[AxiomMath/DedekindZetaZeroFree](https://github.com/AxiomMath/DedekindZetaZeroFree)
是第一项的配套形式化来源，并非额外的独立前提。计数定理原文见
[Frei–Sofos–Widmer 定理 1.1](https://arxiv.org/html/2610.18491v2#Thmtheorem1.1)。

### 4.2 省略算法后的实现接口

`PrimeCountingAlgorithmCertificate C₀` 要求存在 complexitylib 的一台 `NTM`、一个
多项式时间界，使所有分支按时停机，且每个输入的接受概率等于
`primeCountingAcceptance C₀ x`。

这个接受概率由具体有限见证比例定义，正次数本原输入的分母为 `2^(2m+5)`，不是任意
给定的正确性谓词。证书只承担机器实现和运行时间；以下性质由 Lean 单独证明：

- 接受概率处于 `[0,1]`。
- 接受概率严格大于 `1/2` 当且仅当 `x ∈ IrredLang`。
- 由该机器和数学正确性推出 `PP`，再推出 `PSPACE`。

**证书的存在性尚未证明。** 它属于用户允许省略的算法步骤，须与外部文献前提分别列出。
最终定理不是“只给外部解析前提就已构造概率机”的声明。

证书主要对应原论文 **§3.7（PDF 第 13 页）**／独立稿 **§7** 的多数机：固定长度猜测
`p,a,b`，再用三个模式位和补位位实现 `#accept−#reject=2(3P−2A)`。这些有限集合计数
恒等式和判据正确性已证明；证书保留输入预处理、素性测试、模求值、随机分支及多项式
运行时间的实际机器实现。该节多项式时间素性测试的引用是 **Agrawal–Kayal–Saxena，
PRIMES is in P，Annals of Mathematics 160 (2004), 781–793**，原论文 **[1]**／独立稿
**[5]**；它包含在省略的算法实现范围内，没有另设一个 AKS 前提参数。

原论文 **§3.6（PDF 第 12 页）**／独立稿 **§6** 是确定性双重枚举算法：依次枚举
`p<X` 和 `a<p`，累计 `P,A`，按 `2A<3P` 接受，直接提供多项式空间路线。它允许
试除判素，并不要求每条完整执行路径为多项式时间，因此不是当前 `PP` 算法证书的
实现对象。当前最终 `PSPACE` 定理沿已证明的库定理 `PP_subset_PSPACE` 得到。

独立稿 **[4]**／原论文 **[15]** 的 Milne，*Algebraic Number Theory*，第 3 章，提供
好素数处分解的数论背景；当前内部桥接已在 Lean 中完成，不作为最终定理的额外假设。

### 4.3 内部数学前提已经消去的位置

较早的中间定理 `integer_prime_root_average` 仍显式接收判别式预算、好素数对应和
异常集合大小。当前主链调用的是
`integer_prime_root_average_concrete`，它从实际因子和数域证明并填入这些内部数据。
因此，内部平均估计和不可约判据没有被转移到外部前提里。

## 5. 额外已验证的算法数学性质

虽然允许省略机器实现，仓库仍有以下已证明的辅助结果：流式循环等于真实的 `(P,A)`
计数；内外循环前缀的计数器范围和位长界；二分幂、稀疏多项式及导数求值的正确性；
实际剩余类扫描与 `ν+μ` 的对应。这些结果有助于将来构造机器证书。

这些函数中有 `noncomputable` 定义；值的正确性和数学位长界不等于 complexitylib
机器及其时间／空间资源界已经实现。最终 `PSPACE` 结论目前沿 `PP ⊆ PSPACE` 得到，
并未另外构造论文第 3.6 节的确定性枚举机器。

## 6. 验证记录

最近一次完整验证包含本报告列出的最终定理，环境为 Lean `v4.34.0-rc2`：

| 检查 | 结果 |
|---|---|
| `lake build` | 通过，9188 个构建任务 |
| `scripts/Axioms.lean` | 224 个声明的公理审计通过 |
| `scripts/DepAudit.lean` | 208 个入口，传递追踪 78,044 个常量；仅达到标准公理 |
| 标准公理集合 | `propext`、`Classical.choice`、`Quot.sound` |
| 新增证明中的占位与自定义公理 | 无 `sorry`、`admit` 或自定义公理 |
| `scripts/check_vendor.sh` | 38 个 vendored 模块与原提交一致 |

224、208 是历史项目审计入口数，不能解释为第3节独立定理数或完成百分比；
当前发布范围的审计结果以发布记录为准。
原始报告见 [AXIOMS.txt](AXIOMS.txt) 和
[DEP_AUDIT.txt](DEP_AUDIT.txt)。
本次撰写报告未修改 Lean 定理或证明；上述数字来自已完成的构建和审计记录。

公理审计验证的是条件命题及其依赖，不会证明定理参数 `hExternal` 或 `hAlgorithm`
本身存在。

## 7. 尚未纳入本次完成声明的内容

在当前约定下，第 3 节主链没有因缺少外部计数定理仓库而被阻塞。以下内容明确保留边界：

1. 外部零点自由和有效素理想计数定理的独立 Lean 重建：允许引用，本次不要求。
2. `PrimeCountingAlgorithmCertificate` 的实际构造：算法步骤按约定省略。
3. 原论文备注 16／独立稿备注 8.1 的任意固定 `δ>0` 推广：尚未完成一般参数版截断分析。
4. 独立稿第 8 节的 `FPSPACE` 计数扩展：未包含于本次主结论。

适合引用的进度表述是：**在允许的外部计数前提及单独列明的省略算法实现前提下，
第 3 节内部数学推导和整数稀疏不可约性属于 `PP`、`PSPACE` 的最终条件结论均已形式化。**
