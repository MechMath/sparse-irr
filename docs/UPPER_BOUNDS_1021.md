# 2026-10-21 版第 3、4 节：形式化范围及核查历史

**2026-10-22 范围约定：** 论文引用的外部定理可以作为显式前提，无须重证；本文内部的数学
定理和推导须由 Lean 证明；算法步骤和机器实现可以省略；**最终结论必须有 Lean 定理**。
此前把最终 `PP`、`PSPACE` 结论随机器实现一同排除的范围说明已撤回。

第 3 节的统一算术入口为 `Section3Arithmetic.lean` 的
`section3_uniform_arithmetic_conclusion`；最终规范整数语言的 `PP`、`PSPACE` 结论入口为
`Machine/Conclusion.lean` 的 `section3_irreducibility_mem_PP_and_PSPACE_of_external_theorems`。
用户随后要求实现实际机器；`Machine/` 已构造 §3.7 的概率机器，证明多项式时限和精确接受概率。
旧接口中的 `PrimeCountingAlgorithmCertificate C₀` 现由
`primeCountingAlgorithmCertificate_of_binaryPrimalityInFP` 提供，不再是新最终定理的参数。
最终只保留文献计数估计和 AKS 二进制素性判定属于 `FP` 两项外部前提；完整情况见
[第 3 节完成报告](SECTION3_COMPLETION_2026-10-22.md)。后续还已补齐 §3.6 的确定性枚举及
线性空间核心、备注 16 的任意固定正间隙，以及命题 13 的实数截断版本。

**后续进展：** 新增独立版 `sparse_irreducibility_complete_qrh.pdf` 后，第 3 节又补入
112 项公开定理；下文保留首次核查的范围记录，最新完成情况和缺口以
[PRIME_COUNTING_QRH.md](PRIME_COUNTING_QRH.md) 为准。以下主体记录首次核查时的情况，
其中“尚未”或“仍缺少”描述历史快照，不代表当前状态。第 4 节后来已继续形式化，
数学结果及此前条件式 `PSPACE` 定理见
[第 4 节形式化报告](SECTION4_FORMALIZATION_2026-10-22.md)。后续已构造该实现接口，
无实现前提的最终结果及通用 oracle 的实际机器编译见
[完整机器认证报告](SECTION4_MACHINE_CERTIFICATION_2026-10-23.md)。

核查对象：根目录 `1021-AI4Math_Irreducibility.pdf`，18 页。
本文件中的编号均指该版本；此前 7 页版本的对应表见
[IRREDUCIBILITY_AUDIT.md](IRREDUCIBILITY_AUDIT.md)。

## 首次核查结论（历史）

**开始核查时，仓库没有新增两节的上界证明。本次补入 59 项公开定理，
但尚未完成定理 10 的 `SparseIrredZ ∈ PP` 或定理 18 的 `PSPACE` 成员资格证明。**
不能据此把论文这两节或新版主定理标为“全部形式化完成”。

新代码入口是 `import SparseIrred.UpperBounds`，根入口 `import SparseIrred` 也已包含它。
命名空间统一为 `SparseIrred.UpperBounds`。所有已提交到工作区的证明均经过 Lean 检查；
没有添加未证明的公理、`sorry` 或 `admit`。

## 第 3 节（首次核查快照）

| 内容 | 已验证的 Lean 入口 | 范围 |
|---|---|---|
| 常数、零、单位及非原始多项式的预处理 | `integer_irreducible_boundary` | 整数常数不可约当且仅当绝对值为素数；正次数时不可约当且仅当原始且在 `ℚ[X]` 中不可约。包含负素数常数。 |
| 式 (29)：`μ ≤ ν ≤ n` | `primitive_modular_root_bounds` | 对所有素数成立，包括次数下降的素数。 |
| 式 (31)--(33)：重复因子统计量 | `factorStatistic_bounds`、`factorStatistic_eq_one_iff`、`integer_factorStatistic_eq_one_iff` | `ρ` 从真正的规范不可约因子多重集定义；证明 `1 ≤ ρ ≤ deg f`，以及 `ρ = 1 ↔ Irreducible f`，没有平方自由假设。 |
| 式 (34)：好约化素数处的带权根计数 | `weighted_root_count` | 在约化因子两两互素、可分的条件下，证明 `ν_f+μ_f = ∑ᵢ(1+[mᵢ≥2])ν_hᵢ`。不额外排除整除 `mᵢ` 的素数。 |
| 式 (42)：显式截断参数的放大不等式 | `cutoff_amplification` | 使用论文的 `U = 2^20 C₀ n²(Δ+1)²`、`ell = ceil(log₂ U)`、`k=4 ell`，保留原常数。 |
| 截断参数的二进制长度 | `cutoffLog_le` | `ell ≤ 20+clog₂ C₀+2clog₂ n+2clog₂(Δ+1)`。尚未接到原稀疏编码长度 `L`。 |
| 推论 15 的数值推理 | `integer_irreducible_iff_root_threshold_of_approximation` | **显式以四分之一误差估计为假设**，据此证明不可约当且仅当 `2A<3P`。这不是定理 10 的无条件证明。 |
| §3.6 的计数器范围 | `prime_counter_bounds` | 对实际的模素数根计数，证明 `P≤X`、`A≤2 deg(f) X`。尚未实现空间受限的 TM 循环。 |
| §3.7 的八种模式和补位位 | `majorityGadget_balance`、`majorityGadget_majority_iff` | 接受数减拒绝数恰为 `2(3P−2A)`，严格多数恰好对应 `2A<3P`；相等时拒绝。 |

`primeRootSum` 和 `primeCountBelow` 使用 `p<X`，与 §3.6 的循环一致。
论文分析部分使用 `p≤X`；应用到 `X=2^m`、`m≥2` 时端点不是素数。
这个端点转换尚未作为连接引理补入，不能忽略它而直接声称分析估计已覆盖代码定义。

首次核查时以下部分仍缺少证明：

1. §3.1 的零点自由区在当前项目依赖中的接入，以及统一有效素理想计数估计 (24)、(25)。
2. 引理 11 的 Mahler 测度、非首一多项式判别式及异常素数数目界；引理 12 的素理想对应。
3. 命题 13 的全局误差估计、引理 14 的素数数目下界 (43) 和四分之一误差 (44)。
   目前只证明了引理 14 的初等放大不等式和截断指数长度界。
4. 稀疏输入的正规化、模幂、导数求值、素性判断及其时间/空间界；多数票谓词的实际
   见证计数与 `P`、`A` 的对应；将计数构造编译为 complexitylib 的有时限 NTM。
5. 最终的 `IrredLang ∈ Complexity.PP`。库已有 `Complexity.PP_subset_PSPACE`，
   但它需要先证明这里的 `PP` 成员资格，不能单独代替该证明。

### 解析数论依赖的具体情况

论文引用的公开项目
[AxiomMath/DedekindZetaZeroFree](https://github.com/AxiomMath/DedekindZetaZeroFree)
提供了 `Solution/DedekindZetaSolution.lean` 中的 `DedekindZetaZeroFree.main`。
它给出 Dedekind zeta 延拓函数在 `Re(s)>31/32`、`s≠1` 时非零的结论。
核查时该项目使用 Lean `v4.35.0-rc3`；本仓库是 `v4.34.0-rc2`，且 mathlib 版本不同。
因此它尚未成为本仓库中可以导入使用的依赖。

对论文引用的 Frei--Sofos--Widmer 有效估计，当前依赖中未找到相应 Lean 证明；
没有把文献引用转成自定义公理。零点自由区本身也不能直接替代这项有效估计。
按最新约定，这些被引用外部结果可以作为定理的显式参数，未重证它们不再构成本次缺口。

## 第 4 节（首次核查快照）

| 内容 | 已验证的 Lean 入口 | 范围 |
|---|---|---|
| 矩阵幂的逐元素平衡递归 | `powerEntry_eq` | 包含指数 `0`、`1`，以及一般半分递归；适用于任意半环。 |
| 有序矩阵连乘的逐元素平衡递归 | `productEntry_eq` | 保留非交换乘法顺序。 |
| 递归深度的数值界 | `splitDepth_le_of_le_pow`、`splitDepth_le_log` | 深度 `≤log₂ e+2`；这是递归深度的数学界，尚不是 TM 工作带空间界。 |
| 任意特征的无除法行列式算法 | `determinantEntry_eq_det` | 按需计算 Bird 转移矩阵幂的元素，结果等于 `Matrix.det`；包含空行列式。 |
| 平方自由筛选 | `resultant_derivative_ne_zero_iff` | `Res(f,f') ≠ 0 ↔ Squarefree f`，适用于任意有限域，包含常数导数。 |
| 零导数分支 | `not_irreducible_of_derivative_eq_zero` | 正次数且导数为零时不能不可约。 |
| 有限域扩张中的 Frobenius 固定点 | `pow_card_eq_self_iff_scalar`、`finrank_frobeniusFixedSpace_field` | 固定元素恰为底域，固定空间维数为 1。 |
| Berlekamp 不可约判据 | `irreducible_iff_frobeniusFixedSpace_finrank` | 对实际商代数 `AdjoinRoot f = K[X]/(f)` 证明；反向用互素因子产生的非平凡幂等元。没有假设 CRT 结论。 |
| 式 (48) 和伴随矩阵系数入口 | `frobeniusMatrix_entry`、`generator_matrix_entry` | Frobenius 矩阵元素为 `powerEntry C (q*j) i 0`；乘以生成元的矩阵有论文所需的系数形式。 |
| 式 (49) 的秩判据 | `irreducible_iff_frobeniusMatrix_rank` | 平方自由正次数 `f` 不可约当且仅当 `rank(B-I)=deg(f)-1`。未单独证明一般因子数 `r` 等于固定空间维数。 |
| 删行删列子式测试 | `rank_eq_iff_exists_deleted_minor` | 在秩上界下，秩为 `n-1` 当且仅当某个删行删列子式非零。 |
| 所有代数测试的组合 | `irreducible_iff_resultant_and_minor`、`finiteFieldDecision_correct` | 有限域上所有多项式的语义正确性，包含零、常数、一次及非平方自由输入。 |

### 行列式路线与论文的差异

论文用 Berkowitz 的 Toeplitz 连乘恒等式 (47)。当前 mathlib 已证明 Bird 的无除法行列式
算法，因此采用另一条在任意特征都成立的路线：

* 把 Bird 的一步迭代表示成作用于矩阵元素坐标的 `n² × n²` 线性变换 `birdTransition A`；
* 一个转移元素只需要下标比较及原矩阵的两个元素；
* 证明该转移矩阵的幂与 Bird 迭代完全一致，再用 `powerEntry` 求最终所需的元素。

这里没有把稠密 Bird 实现的多项式时间直接解释成稀疏输入的多项式空间。
实际实现、工作带空间估计及转移矩阵的二进制下标编码仍待完成。
式 (47) 本身没有形式化；`determinantEntry_eq_det` 提供所需行列式的替代代数算法。

以下部分仍缺少证明：

1. 有限域输入语言及其编码：素数特征、扩张次数、定义扩张的不可约多项式、系数与
   指数的稀疏二进制表示，以及非法输入的处理。`K`、`Field K`、`Fintype K` 是数学接口，
   不等于已证明均匀复杂性界的输入表示。
2. 有限域运算、稀疏系数查询、Sylvester 矩阵及 Frobenius 子式的空间受限入口。
3. `powerEntry`、`determinantEntry`、子式枚举及这些入口在 complexitylib TM 模型中的实现，
   包括有限求和的顺序执行、存储复用及所有运行前缀的多项式空间界。
4. 最终的、关于上述编码语言的 `Complexity.PSPACE` 成员资格，即定理 18 的复杂性结论。

`finiteFieldDecision` 是一个带有 `noncomputable` 数学接口的语义测试，
**不应当被引用为已经实现的均匀多项式空间图灵机**。

## 验证入口

```sh
lake build
lake env lean scripts/Axioms.lean
lake env lean scripts/DepAudit.lean
scripts/check_vendor.sh
git diff --check
```

`scripts/Axioms.lean` 与 `scripts/DepAudit.lean` 已包含本页 59 项公开定理和独立版本后续
补充的 112 项定理。报告分别保存在 `docs/AXIOMS.txt`、`docs/DEP_AUDIT.txt`。
该历史快照的检查结果：`lake build` 通过（9126 jobs），全部 202 项公理检查通过，
186 个入口的传递闭包含 72,352 个常量，仅达到 `propext`、`Classical.choice`、`Quot.sound`。
38 个 vendored 模块与原提交完全一致；`git diff --check` 通过。
这些历史检查认证当时已写出的证明，不认证后来新增模块，也不证明外部数学前提或算法实现证书。
当前最终包装的构建与审计结果应以更新后的报告为准。
