# 论文第2、3节：编号与 Lean 入口

论文：**Irreducibility Testing of Sparse Polynomials over Integers is NP-hard and Probabilistic Polynomial Time**。
核对日期：2026-10-27；编号对应归档的18页论文版本。
不是7页的 `AI4Math_Irreducibility.pdf`，也不是独立计数稿。
论文 PDF 和未对应此版本的 TeX 草稿不是构建依赖，源码发布包不包含这些本地草稿。

统一导入 `SparseIrred`。本表中 `I.` = `SparseIrred.Irreducibility`，
`UB.` = `SparseIrred.UpperBounds`。当前发布只包含整数不可约性的第2、3节。
源码文件中的早期编号注释未全部改写；例如 `Irreducibility.lean` 的旧定理2–引理7对应
本稿的定理4–引理9。

## 编号声明

| 论文 | 内容 | 主要 Lean term／源码 | 前提和覆盖 |
|---|---|---|---|
| 例1 | `X^p−1` 的完整因式分解输出长度障碍 | 没有专门声明 | 说明性例子未单独形式化，不将其算作已证明 Lean 定理。 |
| 定理2 | 整数硬度与 `PP`、`PSPACE` 上界 | `I.irreducibility_hardness`；`UB.section3_irreducibility_mem_PP_and_PSPACE_of_external_theorems` | 硬度无条件；上界使用下述外部输入。 |
| 定理4 | 四项硬度结论，含一次 oracle 查询与 `P=NP` 推论 | `I.irreducibility_hardness`，[`Irreducibility.lean`](../SparseIrred/Irreducibility.lean) | many-one coNP-hardness 与一次查询 Turing NP-hardness 明确区分。 |
| 引理5 | SAT 载体、互素性与单位根 | `I.satisfiability_encoding` | 任意 gap 的单位根刻画；包含载体的非零与倒数对称性。 |
| 定理6 | gap 判据、倒数乘积刚性及不可约性 | `I.ljunggren_gapPoly`、`I.irreducible_gapPoly` | 专门化的 FFK 证明，非额外外部假设。 |
| 引理7 | 同时逼近、正余数及唯一商 | `I.exists_shifted_residue_modulus` | 包括严格不等式和唯一性。 |
| 引理8 | 最小公倍数、素数计数及编号界 | `I.lcm_primeCounting_bounds`、`I.prime_index_bounds` | 内部证明所需数值界。 |
| 引理9 | 稀疏归约的时间和输出长度 | `I.polynomial_time_sparse_reduction` | 实际机器及多项式时间、输出长度。 |
| 定理10 | 整数 `PP`、`PSPACE` 与确定性枚举 | `UB.section3_irreducibility_mem_PP_and_PSPACE_of_external_theorems`；`UB.Machine.section3_deterministic_streaming_mem_PSPACE` | 外部计数估计及 AKS；另有预处理后线性空间核心。 |
| 引理11 | 判别式和异常素数界 | `UB.integerFactorRootField_logDiscriminant_le`、`UB.integerFactorIndex_weighted_fieldLogDiscriminant_le`、`UB.integerSquarefreeExceptionalPrimes_card_le` | 包含非首一整正规化；不是外部参数。 |
| 引理12 | 模根与次数一素理想对应 | `UB.polynomialRoot_nonmonic_rootCount_eq_degreeOnePrimesOver`、`UB.integerFactorization_good_prime_root_weight_eq_degreeOne` | 真实数域和素理想上的对应。 |
| 命题13 | 平均误差式 (39) | `UB.integer_prime_root_average_concrete_real` | 所有实数 `X>2`；由外部计数输入推出。 |
| 引理14 | 截断放大、素数下界、误差和位数 | `UB.cutoff_amplification`、`UB.prime_count_lower_at_cutoff`、`UB.relative_error_lt_quarter_of_counting_estimates`、`UB.inputCutoffExponent_le_raw_length` | 内部数值推导及输入长度界。 |
| 推论15 | 不可约性等价于 `2*A < 3*P` | `UB.integer_irreducible_iff_primeCounting_threshold_of_uniform_estimate` | 接受外部计数估计，内部证明阈值。 |
| 备注16 | 任意固定正间隙 | `UB.GeneralGap.section3_irreducibility_mem_PP_and_PSPACE_of_positive_gap` | 固定 `δ>0`，不是随输入缩小的间隙。 |

因此，发布范围是这些编号数学结果及其实现。它不表示已经重新证明所有引用文献，或将
每一条背景叙述、例子和开放问题都转成 Lean 声明。

## 公式和算法

| 位置 | 已证明的主要内容 | 详细对应 |
|---|---|---|
| 第2节 | SAT→稀疏载体、FFK gap、归约及实际复杂性下界 | [`Irreducibility.lean`](../SparseIrred/Irreducibility.lean)、[旧硬度核对表](IRREDUCIBILITY_AUDIT.md)；旧编号按上表转换。 |
| 第3节式 (29)–(44) | 模根、重因子统计、好约化、判别式、平均估计、截断和阈值 | [第3节 term 表](SECTION3_LEAN_MAP.md)。 |
| §3.6 | 确定性枚举、二进制寄存器与空间界 | [第3节完成报告](SECTION3_COMPLETION_2026-10-22.md)。 |
| §3.7 | 严格多数接受的实际 NTM、预处理、精确接受概率、多项式时限 | [机器实现报告](SECTION3_MACHINE_IMPLEMENTATION_2026-10-22.md)。 |

§3.6 的 `section3_linear_streaming_core` 从明确预处理好的 `section3CoreStart` 出发。
全输入 `PSPACE` 入口和这一线性空间核心是不同规格；报告不把后者说成从任意原始输入
开始的端到端线性空间机器。

## 外部引用的准确编号

以下编号来自本目标18页稿，不沿用独立稿的参考文献编号。

| 引用 | 论文用途 | Lean 处理 |
|---|---|---|
| **[1] Agrawal–Kayal–Saxena**, *PRIMES is in P* (2004) | §3.7 的多项式时间素性判定 | 显式 `BinaryPrimalityInFP` 参数。 |
| **[6] Cureton–Thorner**, *A quasi-Riemann hypothesis for Dedekind zeta functions*, v2 | §3.1，式 (22) 的零点自由输入 | 计数前提的文献依据；未在本项目重证此独立解析定理。 |
| **[9] Frei–Sofos–Widmer**, *Some applications of the quasi-Riemann hypothesis to class groups and small generators of number fields*, Theorem 1.1, v2 | §3.1，式 (23) 的有效计数 | 通过 `EffectivePrimeIdealEstimate`／`EffectivePrimeIdealEstimateReal` 接收其在零点自由输入下的计数结论。 |
| **[2] AxiomMath/DedekindZetaZeroFree** | 外部零点自由形式化 | 文献记录，未作为此仓库依赖导入。 |
| **[15] Milne**, *Algebraic Number Theory*, Chapter 3 | 引理12的 Dedekind 分解理论 | 相关结果已由依赖库和本项目推导；不是最终额外参数。 |

最终整数上界假设的是**有效计数结论**，不是从裸零点自由命题到计数估计的已证明 Lean
桥接。本文的平均估计、阈值和最终上界均在此之后内部证明。
目标稿的 **[3] Cantor–Zassenhaus** 是稠密因式分解文献，不是计数前提。

## 验证

入口声明及传递依赖通过 Lean 内核检查；当前检查命令和结果见
[发布记录](RELEASE_2026-10-27.md)、[公理输出](AXIOMS.txt) 和 [依赖闭包](DEP_AUDIT.txt)。
历史报告保留当时状态；不得将其中“尚未完成”字样直接当成当前缺口，或将旧的兼容接口
误读为当前最终定理的额外前提。
