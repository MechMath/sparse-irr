# 第 3 节：论文定理、数学符号与 Lean term 对应表

核对日期：2026-10-22。配套说明见
[第 3 节最新完成报告](SECTION3_COMPLETION_2026-10-22.md)；
[§3.7 机器实现报告](SECTION3_MACHINE_IMPLEMENTATION_2026-10-22.md) 保留该阶段的细节。
当前新增范围限原论文第 3 节：§3.6、备注 16 与命题 13 的实数截断。

下文“原论文”指 `1021-AI4Math_Irreducibility.pdf`，“独立稿”指
`sparse_irreducibility_complete_qrh.pdf`。表中未写命名空间的 Lean 名称均加前缀
`SparseIrred.UpperBounds.`；`SparseIrred.IrredLang` 等例外写出完整名称。

`theorem` 声明的名称是已由 Lean 检查的证明 term；`def`／`abbrev` 名称是定义或类型接口。
不能把一个 `Prop` 的定义当成该命题已被证明。下表的状态和前提按当前定理声明核对。

## 1. 两套论文编号

| 原论文第 3 节 | 独立稿 | 内容 |
|---|---|---|
| 定理 10，PDF 第 7 页 | 定理 1.1，第 1 页 | `SparseIrredZ ∈ PP ⊆ PSPACE` |
| §3.1，第 8 页 | §1.1–1.2，第 2 页 | 引用的零点自由与有效计数定理 |
| §3.2，第 8–9 页 | §2，第 2–3 页 | 模根、重复根和因子统计量 |
| 引理 11，第 9–10 页 | 引理 3.1，第 3–4 页 | 判别式预算和异常素数界 |
| 引理 12，第 10 页 | 引理 3.2，第 4 页 | 根与次数一素理想对应 |
| 命题 13，第 10–11 页 | 命题 4.1，第 4–5 页 | 全局平均误差界 |
| 引理 14，第 11–12 页 | 引理 5.1，第 5 页 | 截断、素数下界、四分之一误差和位长 |
| 推论 15，第 12 页 | 推论 5.2，第 6 页 | 精确不可约性判据 |
| §3.6，第 12 页 | §6，第 6 页 | 确定性流式算法 |
| §3.7，第 13 页 | §7，第 6–7 页 | 严格多数及 `PP` 结论 |
| 备注 16，第 13 页 | 备注 8.1，第 8 页 | 任意固定正间隙的推广，现已有实际机器和最终复杂性定理 |

原论文公式 `(21)`–`(46)` 对应独立稿 `(1)`–`(26)`，编号差为 20。
特别地，局部根界是原论文 **(29)**／独立稿 (9)；原论文 (28) 是 `A_f(X)`、`P(X)` 的定义。

## 2. 定理与证明 term

“已证明”允许声明中列出的标准数学输入条件；“外部前提”“算法接口”不表示其存在性
已经由本仓库证明。主链最终调用实际输入版本，抽象中间定理在相应行明确标注。

### 2.1 输入、局部根与因子统计量

| 论文位置／数学结论 | Lean term | 源码 | 前提与状态 |
|---|---|---|---|
| §3 开头／独立 §1：整数常数、零、单位及本原性边界 | `integer_irreducible_boundary` | [IntegerBoundary:32](../SparseIrred/UpperBounds/IntegerBoundary.lean#L32) | 已证明；任意 `f : ℤ[X]`，分次数为零和正次数两种情形。 |
| 稀疏输入的 `log(n+2)`、`log(S+2)` 为 `O(L)` | `raw_input_log_bounds` | [RawInputBounds:25](../SparseIrred/UpperBounds/RawInputBounds.lean#L25) | 已证明；任意原始项表，长度用原始编码。 |
| 原 (29)／独立 (9)：`μ≤ν≤n` | `primitive_modular_root_bounds` | [ModularRoots:39](../SparseIrred/UpperBounds/ModularRoots.lean#L39) | 已证明；`f` 本原，`p` 素数；包含次数下降素数。 |
| 原 (31)–(32)／独立 (11)–(12)：`1≤ρ≤n` | `factorStatistic_bounds` | [FactorStatistic:97](../SparseIrred/UpperBounds/FactorStatistic.lean#L97) | 已证明；域上正次数多项式，实际规范因子多重集。 |
| 原 (33)／独立 (13)：整数本原输入 `ρ=1 ↔ 不可约` | `integer_factorStatistic_eq_one_iff` | [FactorStatistic:138](../SparseIrred/UpperBounds/FactorStatistic.lean#L138) | 已证明；`f` 本原，统计量作用于其 `ℚ[X]` 像。 |
| 原 (32)／独立 (12)：`Σwᵢ[Kᵢ:ℚ]≤n` | `integerFactorIndex_weighted_finrank_sum_le` | [PrimeAverageInstantiation:49](../SparseIrred/UpperBounds/PrimeAverageInstantiation.lean#L49) | 已证明；实际整数因子及其根域，`f` 本原。 |
| 原 (34)／独立 (14)：好约化处 `ν+μ=Σwᵢνᵢ` | `weighted_root_count` | [GoodReductionRoots:84](../SparseIrred/UpperBounds/GoodReductionRoots.lean#L84) | 已证明的抽象代数引理；给定两两互素、可分的有限因子族及其分解。实际因子实例见下表。 |

### 2.2 外部估计、判别式与素理想

| 论文位置／数学结论 | Lean term | 源码 | 前提与状态 |
|---|---|---|---|
| 原 (23)／独立 (3)：外部有效计数结论 | `EffectivePrimeIdealEstimate` | [ExternalPrimeIdealEstimate:34](../SparseIrred/UpperBounds/ExternalPrimeIdealEstimate.lean#L34) | **外部 `Prop` 接口**；对所有数域和整数 `X>2` 量化，未在本仓库重证。 |
| 原 (24)／独立 (4)：固定 `δ=1/32` | `effectivePrimeIdealEstimate_fixed_gap` | [ExternalPrimeIdealEstimate:48](../SparseIrred/UpperBounds/ExternalPrimeIdealEstimate.lean#L48) | 已证明；由 `δ=1/32` 时的外部计数前提作数值化简，得到 `UniformPrimeIdealEstimate C`。 |
| 原 §3.1／独立 §1.2：先固定统一整数 `C₀≥1` | `exists_integer_uniform_primeIdeal_estimate` | [ExternalPrimeIdealEstimate:65](../SparseIrred/UpperBounds/ExternalPrimeIdealEstimate.lean#L65) | 已证明；前提是存在正实常数的外部有效估计，常数在输入之前选定。 |
| 原 (25)／独立 (5)：有理素数计数估计 | `rational_primeCount_estimate` | [ExternalPrimeIdealEstimate:75](../SparseIrred/UpperBounds/ExternalPrimeIdealEstimate.lean#L75) | 已证明；将统一数域估计特化到实际数域 `ℚ`。 |
| 引理 11／独立引理 3.1：`1≤M(g)≤M(f)≤S` | `integer_divisor_mahler_bounds` | [IntegerMahlerBounds:61](../SparseIrred/UpperBounds/IntegerMahlerBounds.lean#L61) | 已证明；`f≠0`，`g∣f`，实际整数多项式。 |
| 非首一因子整正规化后，数域判别式整除多项式判别式 | `polynomialRoot_numberField_discr_dvd` | [PowerBasisDiscriminant:153](../SparseIrred/UpperBounds/PowerBasisDiscriminant.lean#L153) | 已证明；正次数且在 `ℚ` 上不可约，使用实际 `NumberField.discr`。 |
| 引理 11／独立引理 3.1：逐因子域判别式界 | `integerFactorRootField_logDiscriminant_le` | [PrimeAverageInstantiation:572](../SparseIrred/UpperBounds/PrimeAverageInstantiation.lean#L572) | 已证明；真实因子 `i`，本原 `f`；含 Mahler、Vandermonde 和整正规化推导。 |
| 原 (36)／独立 (16)：`ΣwᵢlogDᵢ≤n²Δ` | `integerFactorIndex_weighted_fieldLogDiscriminant_le` | [PrimeAverageInstantiation:660](../SparseIrred/UpperBounds/PrimeAverageInstantiation.lean#L660) | 已证明的实际输入版本；`f` 本原且正次数。 |
| 原 (37)／独立 (17)：异常素数数目 `≤2nΔ` | `integerSquarefreeExceptionalPrimes_card_le` | [PrimeAverageInstantiation:108](../SparseIrred/UpperBounds/PrimeAverageInstantiation.lean#L108) | 已证明；集合取实际 `lc(F)Disc(F)` 的不同素因子。 |
| 引理 12／独立引理 3.2：非首一因子的根与次数一素理想对应 | `polynomialRoot_nonmonic_rootCount_eq_degreeOnePrimesOver` | [PowerBasisDiscriminant:196](../SparseIrred/UpperBounds/PowerBasisDiscriminant.lean#L196) | 已证明；正次数、在 `ℚ` 上不可约、好素数；包括可逆变量变换。 |
| 好素数对应的真实因子族版本 | `integerFactorization_good_prime_root_weight_eq_degreeOne` | [PrimeAverageInstantiation:522](../SparseIrred/UpperBounds/PrimeAverageInstantiation.lean#L522) | 已证明；本原正次数 `f`，素数 `p` 在实际异常集合外；内部约化条件已自动证明。 |
| 高剩余次数贡献 `≤n√X` | `integerFactor_higher_degree_bound` | [PrimeAverageInstantiation:711](../SparseIrred/UpperBounds/PrimeAverageInstantiation.lean#L711) | 已证明；实际因子域族，`f` 本原。 |
| 命题 13／独立命题 4.1：抽象误差求和 | `prime_root_average_bound` | [PrimeAverage:150](../SparseIrred/UpperBounds/PrimeAverage.lean#L150) | 已证明的中间定理；显式接收局部估计及代数预算，供实际版本调用。 |
| 原 (39)／独立 (19)：实际输入的全局平均误差 | `integer_prime_root_average_concrete` | [PrimeAverageInstantiation:828](../SparseIrred/UpperBounds/PrimeAverageInstantiation.lean#L828) | 已证明；本原正次数 `f`、`C≥0`、`X>2`、统一外部估计。内部判别式／异常集合／好素数假设均已消去。 |

原 (22)／独立 (2) 的零点自由结论没有在本项目另建解析证明入口；当前直接接收其与
引用的有效估计所提供的 `EffectivePrimeIdealEstimate (1/32) C`。因此没有一个已证明的
Lean term 在本项目中从裸零点自由陈述推出该有效计数估计。

### 2.3 截断、判据与多数见证

| 论文位置／数学结论 | Lean term | 源码 | 前提与状态 |
|---|---|---|---|
| 原 (42)／独立 (22)：截断放大不等式 | `cutoff_amplification` | [PrimeCutoff:48](../SparseIrred/UpperBounds/PrimeCutoff.lean#L48) | 已证明；`C₀,n≥1`，保留 `2^20` 等论文常数。 |
| 原 (43)／独立 (23)：截断处素数计数下界 | `prime_count_lower_at_cutoff` | [CutoffError:165](../SparseIrred/UpperBounds/CutoffError.lean#L165) | 已证明的数值引理；接收素数误差和对数积分下界。 |
| 原 (45)／独立 (25)：三项误差数值控制 | `cutoffError_lt_quarter_at_cutoff` | [CutoffError:302](../SparseIrred/UpperBounds/CutoffError.lean#L302) | 已证明；`C₀,n≥1`，使用论文选定截断。 |
| 原 (44)／独立 (24)：由计数误差推出 `|A/P−ρ|<1/4` | `relative_error_lt_quarter_of_counting_estimates` | [CutoffError:282](../SparseIrred/UpperBounds/CutoffError.lean#L282) | 已证明的抽象数值引理；计数估计在主链中由真实平均界填入。 |
| 截断指数 `m=log₂X` 相对原始长度为线性 | `inputCutoffExponent_le_raw_length` | [RawInputBounds:53](../SparseIrred/UpperBounds/RawInputBounds.lean#L53) | 已证明；任意原始项表，`m≤128*(38+clog₂C₀)+768L`。 |
| 原 (46)／独立 (26)，推论 15／推论 5.2 | `integer_irreducible_iff_primeCounting_threshold_of_uniform_estimate` | [PrimeAverageInstantiation:874](../SparseIrred/UpperBounds/PrimeAverageInstantiation.lean#L874) | 已证明；本原正次数 `f`、`C₀≥1`、统一外部估计；结论为实际截断上的 `Irreducible f ↔ 2A<3P`。 |
| 分析的 `p≤X` 与循环的 `p<X` 对接 | `inputCutoff_counts` | [PrimeCutoffCounts:52](../SparseIrred/UpperBounds/PrimeCutoffCounts.lean#L52) | 已证明；`C₀≥1`、正次数；实际截断是大于 2 的合数。 |
| §3.7／独立 §7：`#R⁺=P` | `positivePrimeWitness_count` | [PrimeWitnessCount:67](../SparseIrred/UpperBounds/PrimeWitnessCount.lean#L67) | 已证明；`X>0`，实际有限见证域。 |
| §3.7／独立 §7：`#R⁻=A` | `negativePrimeWitness_count` | [PrimeWitnessCount:130](../SparseIrred/UpperBounds/PrimeWitnessCount.lean#L130) | 已证明；任意 `f,X`，含额外的重复根贡献。 |
| 八种模式的接受数减拒绝数 `=2(3P−2A)` | `majorityGadget_balance` | [MajorityCount:78](../SparseIrred/UpperBounds/MajorityCount.lean#L78) | 已证明；一般有限见证上的多数构造。 |
| 见证总数 `=2^(2m+5)` | `primeWitness_choice_count` | [PrimeWitnessCount:155](../SparseIrred/UpperBounds/PrimeWitnessCount.lean#L155) | 已证明；两段 `m` 位整数及五个附加位。 |
| 二进制见证严格多数 `↔2A<3P` | `primeWitness_binary_majority_iff` | [PrimeWitnessCount:163](../SparseIrred/UpperBounds/PrimeWitnessCount.lean#L163) | 已证明；`X=2^m`，相等时拒绝。 |
| 全部原始输入上的计数判据，含边界分支 | `rawList_irreducible_iff_primeCounting_test` | [RawPrimeCountingDecision:19](../SparseIrred/UpperBounds/RawPrimeCountingDecision.lean#L19) | 已证明；任意 `ITerms`，`C₀≥1`，统一外部估计。 |
| 全部原始输入上的见证多数判据 | `rawList_irreducible_iff_primeCounting_majority` | [RawPrimeCountingDecision:51](../SparseIrred/UpperBounds/RawPrimeCountingDecision.lean#L51) | 已证明；同上。 |
| 原始输入下多数选择位数为线性 | `rawList_primeCounting_choice_bits_le` | [RawPrimeCountingDecision:73](../SparseIrred/UpperBounds/RawPrimeCountingDecision.lean#L73) | 已证明；任意项表，不需外部估计。 |
| 固定一个常数后对所有输入的统一算术结论 | `section3_uniform_arithmetic_conclusion` | [Section3Arithmetic:37](../SparseIrred/UpperBounds/Section3Arithmetic.lean#L37) | 已证明；只需正实常数外部有效估计的存在性，不需算法证书。 |

### 2.4 最终语言结论与算法边界

| 论文位置／数学结论 | Lean term | 源码 | 前提与状态 |
|---|---|---|---|
| 具体接受概率处于 `[0,1]` | `primeCountingAcceptance_mem_Icc` | [Section3Conclusion:69](../SparseIrred/UpperBounds/Section3Conclusion.lean#L69) | 已证明；任意字符串，无解析或算法前提。 |
| 接受概率 `>1/2 ↔ x∈IrredLang` | `primeCountingAcceptance_gt_half_iff_mem_IrredLang` | [Section3Conclusion:114](../SparseIrred/UpperBounds/Section3Conclusion.lean#L114) | 已证明；统一外部估计、`C₀≥1`；含错误编码和全部边界。 |
| 算法机器与运行时间接口 | `PrimeCountingAlgorithmCertificate` | [Section3Conclusion:131](../SparseIrred/UpperBounds/Section3Conclusion.lean#L131) | `Prop` 定义；其存在性现由下列实际机器定理从 AKS 前提证明。 |
| 固定常数的 `PP` 成员资格 | `irreducibility_mem_PP_of_primeCounting_certificate` | [Section3Conclusion:138](../SparseIrred/UpperBounds/Section3Conclusion.lean#L138) | 已证明条件定理；`C₀≥1`、统一估计及该常数的算法证书。 |
| 固定常数的 `PP` 和 `PSPACE` 成员资格 | `irreducibility_mem_PP_and_PSPACE_of_primeCounting_certificate` | [Section3Conclusion:149](../SparseIrred/UpperBounds/Section3Conclusion.lean#L149) | 已证明；同上，`PSPACE` 使用库中 `PP⊆PSPACE`。 |
| 原定理 10／独立定理 1.1 的旧接口 | `section3_irreducibility_mem_PP_and_PSPACE` | [Section3Conclusion:159](../SparseIrred/UpperBounds/Section3Conclusion.lean#L159) | 保留兼容；外部正实常数估计存在性，加上 `∀C₀≥1` 的算法证书。新主入口消去证书参数。 |
| §3.7 实际机器及时间、概率证书 | `primeCountingAlgorithmCertificate_of_binaryPrimalityInFP` | [Machine/Conclusion](../SparseIrred/UpperBounds/Machine/Conclusion.lean) | 已证明；唯一前提是 `BinaryPrimalityInFP`，即引用的 AKS 定理。 |
| 原定理 10／独立定理 1.1 的新主入口 | `section3_irreducibility_mem_PP_and_PSPACE_of_external_theorems` | [Machine/Conclusion](../SparseIrred/UpperBounds/Machine/Conclusion.lean) | 外部有效计数估计与 AKS；无算法实现证书参数，结论为 `IrredLang∈PP ∧ IrredLang∈PSPACE`。 |
| `PP ⊆ PSPACE` | `Complexity.PP_subset_PSPACE` | complexitylib 已有定理，由 `Complexitylib.Classes.Containments.PPSubsetPSPACE` 导入 | 复用库内证明；不作为额外的未证明假设。 |

### 2.5 已验证、但不等同于机器实现的算法数学性质

| 论文步骤 | Lean term | 源码 | 当前含义 |
|---|---|---|---|
| §3.6／独立 §6：流式循环得到 `(P,A)` | `primeStreaming_eq_counts` | [PrimeStreaming:137](../SparseIrred/UpperBounds/PrimeStreaming.lean#L137) | 已证明尾递归数学函数的值等于实际计数。 |
| 每个外循环前缀的计数器位长 | `raw_inputCutoff_counter_bits` | [RawInputBounds:84](../SparseIrred/UpperBounds/RawInputBounds.lean#L84) | 已证明原始输入长度下的线性界；非机器工作带证明。 |
| 二分幂与普通幂一致 | `binaryPow_eq_pow` | [SparseModularEval:27](../SparseIrred/UpperBounds/SparseModularEval.lean#L27) | 已证明，任意幺半群。 |
| 稀疏求值正确 | `sparseEval_eq` | [SparseModularEval:94](../SparseIrred/UpperBounds/SparseModularEval.lean#L94) | 已证明，任意项表及交换环中的求值。 |
| 稀疏导数求值正确 | `sparseDerivativeEval_eq` | [SparseModularEval:124](../SparseIrred/UpperBounds/SparseModularEval.lean#L124) | 已证明，含零指数及在零处求值。 |
| 稀疏局部扫描等于模根权重 | `sparseModularRootScan_count` | [SparseModularEval:171](../SparseIrred/UpperBounds/SparseModularEval.lean#L171) | 已证明，实际素数 `p`。 |

### 2.6 已验证的 §3.7 实际机器

下表中的 `Machine.` 指 `SparseIrred.UpperBounds.Machine.`。

| 机器环节 | Lean term | 文件 | 状态 |
|---|---|---|---|
| 规范输入检查 | `Machine.validCode_eq_true_iff`、`Machine.validCode_mem_FP` | `Machine/CodeValidation.lean` | 正确性及多项式时间已证明，错误编码拒绝。 |
| 计算截断位数 | `Machine.cutoffUnary_eq`、`Machine.cutoffUnary_mem_FP` | `Machine/CutoffParameters.lean` | 从实际编码计算，不展开指数大小的候选范围。 |
| 二进制模求值及导数 | `sparseEvalModStr_isZero_iff`、`sparseEvalModStr_mem_FP` | `Machine/ModularVerifier.lean` | 正确性与多项式时间均已证明。 |
| 引用的 AKS 定理接口 | `BinaryPrimalityInFP` | `Machine/WitnessFP.lean` | 显式外部前提；原论文 §3.7 [1]／独立稿 [5]。 |
| 八模式确定性验证器 | `Machine.encodedVerifierStr_eq`、`Machine.encodedVerifierStr_mem_FPn` | `Machine/EncodedVerifierFP.lean` | 仅以 AKS 为前提的时间证明；语义正确性无额外前提。 |
| 真正的位串解析与均匀分布 | `seedPrimeChoices_bijective`、`Machine.randomSeedVerifier_eventProb` | `Machine/SeedEncoding.lean`、`Machine/SeedAcceptance.lean` | 对实际解析程序证明双射和精确接受概率。 |
| 实际固定长度随机猜测机器 | `Machine.fixedGuessVerifyNTM` | `Machine/GuessPipeline.lean` | 具体 NTM 转移函数；强制继续，仅写位步骤使用随机选择。 |
| 完整执行及接受概率 | `Machine.fixedGuessVerifyNTM_acceptProb` | `Machine/GuessMachine.lean` | 包含初始化、回卷、猜测、构造输入及验证的整段 trace。 |
| 输入填充及确定性预处理组合 | `Machine.paddedPrimeVerifier_eventProb`、`Machine.exists_polynomial_precompose` | `Machine/PaddedVerifier.lean`、`Machine/Precompose.lean` | 实际机器组合保持精确概率和多项式时间。 |

### 2.7 原论文 §3.6 的实际确定性机器

下列 `Machine.` 前缀仍指 `SparseIrred.UpperBounds.Machine.`。线性空间使用
`Cfg.WithinDecisionSpace`，包含输出磁带；`binaryRoutine_bit_decisionSpace` 证明单比特输出机器
所有运行前缀的输出头也受界，不能将工作寄存器位长直接当作整机空间证明。

| 论文环节 | Lean term | 文件 | 状态与范围 |
|---|---|---|---|
| 输入磁带与二进制项表解析 | `Machine.inputReadBit_sound`、`Machine.parseTerm70_spec`、`Machine.parseTerm70_space` | `Machine/StreamingBinaryInput.lean`、`StreamingBinaryInputTerm.lean`、`StreamingBinaryInputTermSpace.lean` | 真实 TM；提取有符号系数、指数和余下项表，保持调用者寄存器，全部运行前缀空间受界。 |
| 自行实现的试除判素 | `Machine.binaryPrime_sound`、`Machine.binaryPrime_flag_iff` | `Machine/StreamingBinaryPrimeTotal.lean` | 处理全部自然数；该确定性子程序不使用 AKS。 |
| 模约减、幂与单项式 | `Machine.framedMod_sound`、`Machine.binaryPow_sound`、`Machine.binaryTerm_sound` | `Machine/StreamingBinaryFramed.lean`、`StreamingBinaryPow.lean`、`StreamingBinaryTerm.lean` | 实际寄存器机器、精确算术效果与二进制宽度空间界。 |
| 完整表求值与导数 | `Machine.binarySparseEval` | `Machine/StreamingBinaryEval.lean`、`StreamingBinaryEvalSpace.lean` | 逐项解析并维护正负模累加器；最终真实比较器输出零标志。 |
| 素数／剩余类双循环 | `Machine.coreEnumeration`、`Machine.coreEnumeration_eq_paper_counts` | `Machine/StreamingBinaryCore.lean`、`StreamingBinaryCoreSemantics.lean` | 具体计数循环；与 `P,A` 精确对应，调用的实际 cell 已接上判素与求值子程序。 |
| 最终不等式与输出位 | `Machine.coreVerdict_emitted`、`Machine.coreVerdict_space` | `Machine/StreamingBinaryVerdict.lean` | 实际计算 `2A<3P` 并写出一个判定位，空间保持线性二进制宽度。 |
| 整段核心的线性决策空间与正确性 | `Machine.section3_linear_streaming_core` | `Machine/StreamingLinearCore.lean` | 规范、本原、正次数输入；全部运行前缀 `O(L)`，最终输出不可约性判定。数学判据保留外部计数前提。 |
| 包含外围分支的确定性 `PSPACE` 路线 | `Machine.section3_deterministic_streaming_mem_PSPACE` | `Machine/StreamingTrace.lean` | 全输入枚举路线；其 `FP` 步骤仍显式使用 AKS，与不依赖 AKS 的二进制核心分别记录。 |

### 2.8 备注 16 与命题 13 的完整截断范围

| 原论文结论 | Lean term | 文件 | 前提与范围 |
|---|---|---|---|
| 任意正间隙统一选常数 | `exists_integer_scaled_primeIdeal_estimate` | `GeneralGapEstimate.lean` | 从 `δ>0` 及其外部有效计数估计选固定 `r,C₀`，先于输入量化。 |
| 一般间隙的明确截断与线性位长 | `scaledInputCutoffExponent_le_raw_length` | `GeneralGapDecision.lean` | `m=128*r*cutoffLog C₀(r*n)Δ`，固定 `r,C₀` 时 `m=O(L)`。 |
| 一般间隙的内部误差与决定不等式 | `scaled_relative_error_lt_quarter`、`integer_irreducible_iff_scaledPrimeCounting_threshold` | `GeneralGapError.lean`、`GeneralGapDecision.lean` | 由计数估计证明四分之一误差与不可约性阈值，没有假设内部结论。 |
| 一般间隙的实际概率机器 | `GeneralGap.exists_primeCounting_machine` | `Machine/GeneralGapConclusion.lean` | 从已证字符串程序构造实际 NTM、多项式时间及精确接受概率；判素使用外部 AKS。 |
| 备注 16 最终 `PP`、`PSPACE` | `GeneralGap.section3_irreducibility_mem_PP_and_PSPACE_of_positive_gap` | `Machine/GeneralGapConclusion.lean` | 任意固定 `δ>0`；只要求 `EffectivePrimeIdealEstimate δ C` 的正常数存在性和 AKS。 |
| 实数截断的实际计数语义 | `mem_primesLEReal`、`mem_primeIdealsLEReal`、`primeRootSumLEReal_eq_sum` | `RealCutoff.lean` | 基于 `⌊X⌋₊` 定义并证明恰好计数不超过实数 `X` 的对象。 |
| 命题 13，任意实数 `X>2` | `integer_prime_root_average_concrete_real` | `RealCutoff.lean` | 外部计数定理用实数范围接口 `EffectivePrimeIdealEstimateReal (1/32) C`；内部平均界已证明。 |
| 实数文献接口与整数接口的衔接 | `effectivePrimeIdealEstimateReal_to_integer` | `RealCutoff.lean` | 已证明实数范围文献前提限制到整数后给出旧接口。 |

## 3. 数学符号与定义 term

| 论文对象 | Lean 表达式／定义 | 位置或说明 |
|---|---|---|
| 原始稀疏输入列表 | `SparseDiv.Appendix.ITerms` | [IntTerms:27](../Vendor/SparseDivComplexity/Appendix/IntTerms.lean#L27)，即 `List (ℤ × ℕ)`。 |
| 列表所表示的多项式 | `SparseDiv.Appendix.toPolyZ l` | [IntTerms:30](../Vendor/SparseDivComplexity/Appendix/IntTerms.lean#L30)，项相加，允许重复指数和相消。 |
| 原始输入编码／长度 `L` | `SparseDiv.Appendix.encITerms l`／其 `.length` | [IntTermsString:64](../Vendor/SparseDivComplexity/Appendix/IntTermsString.lean#L64)。 |
| 规范多项式编码 | `SparseIrred.encPoly f` | [Canonical:39](../SparseIrred/Sparse/Canonical.lean#L39)，非零项按指数严格递增。 |
| 规范解码 | `SparseIrred.decodePoly x` | [Canonical:43](../SparseIrred/Sparse/Canonical.lean#L43)，错误或非规范码返回 `none`。 |
| 不可约性语言 `SparseIrredZ` 的本项目表示 | `SparseIrred.IrredLang` | [Canonical:185](../SparseIrred/Sparse/Canonical.lean#L185)，规范码所表示的 `ℤ[X]` 不可约元素。 |
| 次数 `n` | `f.natDegree` | 主链要求正次数；零和常数在外围分支处理。 |
| `S=∥f∥₁` | `integerL1 f` | [SparseInputBounds:56](../SparseIrred/UpperBounds/SparseInputBounds.lean#L56)，:58 证明等于系数绝对值之和。 |
| `Δ=⌈log₂(n+2)⌉+⌈log₂(S+2)⌉+2` | `inputDelta f` | [SparseInputBounds:84](../SparseIrred/UpperBounds/SparseInputBounds.lean#L84)。 |
| 不同不可约整数因子 `hᵢ` | `integerFactors f` | [IntegerFactorFamily:42](../SparseIrred/UpperBounds/IntegerFactorFamily.lean#L42)，取实际规范因子多重集的集合。 |
| 重数 `mᵢ`／权重 `wᵢ` | `integerFactorMultiplicity f h`／`integerFactorWeight f h` | [IntegerFactorFamily:47](../SparseIrred/UpperBounds/IntegerFactorFamily.lean#L47)，权重为 `1+[mᵢ≥2]`。 |
| 平方自由因子乘积 `F` | `integerSquarefreePart f` | [IntegerFactorFamily:56](../SparseIrred/UpperBounds/IntegerFactorFamily.lean#L56)，仅用于证明，不要求机器计算。 |
| 因子域 `Kᵢ` | `IntegerFactorRootField f hf i` | [PrimeAverageInstantiation:30](../SparseIrred/UpperBounds/PrimeAverageInstantiation.lean#L30)，用整正规化生成元构造，域次数等于因子次数。 |
| `log Dᵢ` | `fieldLogDiscriminant (IntegerFactorRootField f hf i)` | [ExternalPrimeIdealEstimate:22](../SparseIrred/UpperBounds/ExternalPrimeIdealEstimate.lean#L22)，实际绝对数域判别式的对数。 |
| `ρ(f)` | `factorStatistic (f.map (Int.castRingHom ℚ))` | [FactorStatistic:92](../SparseIrred/UpperBounds/FactorStatistic.lean#L92)，已证明等于 `Σwᵢ`。 |
| `ν_f(p)` | `rootCount (f.map (Int.castRingHom (ZMod p)))` | [ModularRoots:15](../SparseIrred/UpperBounds/ModularRoots.lean#L15)，在素数假设下使用有限域实例。 |
| `μ_f(p)` | `multipleRootCount (f.map (Int.castRingHom (ZMod p)))` | [ModularRoots:19](../SparseIrred/UpperBounds/ModularRoots.lean#L19)。 |
| 单个素数贡献 `ν+μ` | `primeRootWeight f p` | [IntegerRootCriterion:22](../SparseIrred/UpperBounds/IntegerRootCriterion.lean#L22)，非素数返回零。 |
| 循环中的 `P(X)`／`A_f(X)` | `primeCountBelow X`／`primeRootSum f X` | [IntegerRootCriterion:31](../SparseIrred/UpperBounds/IntegerRootCriterion.lean#L31)，**严格 `p<X`**；论文 `p≤X` 版用 `X+1`，合数端点下相同。 |
| `π_K(X)`／次数一部分 | `primeIdealCountLE K X`／`degreeOnePrimeIdealCountLE K X` | [PrimeIdealComparison:28](../SparseIrred/UpperBounds/PrimeIdealComparison.lean#L28)，均为范数 `≤X`。 |
| 截断参数 `U`／`ℓ` | `cutoffScale C₀ n Δ`／`cutoffLog C₀ n Δ` | [PrimeCutoff:27](../SparseIrred/UpperBounds/PrimeCutoff.lean#L27)，`ℓ=Nat.clog 2 U`。 |
| `m=32k=128ℓ` | `inputCutoffExponent C₀ f` | [SparseInputBounds:128](../SparseIrred/UpperBounds/SparseInputBounds.lean#L128)。 |
| `X=2^m` | `primeCountingCutoff C₀ f` | [PrimeCountingDecision:19](../SparseIrred/UpperBounds/PrimeCountingDecision.lean#L19)。 |
| 正／负见证 `R⁺`、`R⁻` | `positivePrimeWitness X`／`negativePrimeWitness f X` | [PrimeWitnessCount:40](../SparseIrred/UpperBounds/PrimeWitnessCount.lean#L40)，共同域 `PrimeWitness X = Fin X × Fin X × Bool`。 |
| 八模式及补位位的多数谓词 | `majorityGadget positive negative` | [MajorityCount:56](../SparseIrred/UpperBounds/MajorityCount.lean#L56)。 |
| 满足见证数 | `witnessCount R` | [MajorityCount:36](../SparseIrred/UpperBounds/MajorityCount.lean#L36)。 |
| 原始输入的完整判据 | `rawPrimeCountingTest C₀ l`／`rawPrimeCountingMajority C₀ l` | [Section3Arithmetic:16](../SparseIrred/UpperBounds/Section3Arithmetic.lean#L16)，含常数和本原性分支。 |
| 字符串上的有理接受概率 | `primeCountingAcceptance C₀ x` | [Section3Conclusion:38](../SparseIrred/UpperBounds/Section3Conclusion.lean#L38)，解码失败返回零。 |

`raw` 项表上的判据允许非规范项表；最终 `IrredLang` 使用规范编码。当前没有把所有
非规范字符串也定义为该最终语言的合法输入，不能混同这两个接口。

## 4. 如何在 Lean 中查看

统一导入入口：`import SparseIrred.UpperBounds.PrimeCounting`；根入口 `import SparseIrred`
也已包含这些声明。查看主定理的完整类型、证明 term 和公理依赖：

```lean
import SparseIrred.UpperBounds.PrimeCounting

#check SparseIrred.UpperBounds.section3_uniform_arithmetic_conclusion
#check SparseIrred.UpperBounds.section3_irreducibility_mem_PP_and_PSPACE
#print SparseIrred.UpperBounds.PrimeCountingAlgorithmCertificate
#print SparseIrred.UpperBounds.section3_irreducibility_mem_PP_and_PSPACE
#print axioms SparseIrred.UpperBounds.section3_irreducibility_mem_PP_and_PSPACE
```

三个新增范围的直接入口：

```lean
import SparseIrred.UpperBounds.RealCutoff
import SparseIrred.UpperBounds.Machine.GeneralGapConclusion
import SparseIrred.UpperBounds.Machine.StreamingLinearCore

#check SparseIrred.UpperBounds.integer_prime_root_average_concrete_real
#check SparseIrred.UpperBounds.GeneralGap.section3_irreducibility_mem_PP_and_PSPACE_of_positive_gap
#check SparseIrred.UpperBounds.Machine.section3_linear_streaming_core
```

完整批量公理检查入口为 `scripts/Axioms.lean`，传递依赖检查入口为
`scripts/DepAudit.lean`。外部有效计数估计和 AKS 仍是明确参数；算法证书现由机器实现定理构造，
不再是新最终定理的参数。
