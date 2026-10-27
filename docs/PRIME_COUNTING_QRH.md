# 原论文第 3 节：素数计数形式化当前记录

当前范围为根目录 `1021-AI4Math_Irreducibility.pdf` 的第 3 节。
最新完成范围见 [第 3 节完成报告](SECTION3_COMPLETION_2026-10-22.md)。
下方保留早期独立版对应表，便于按旧代码注释定位；本次范围不包括第 4 节和独立稿扩展。

第 3.7 节机器的详细实现见
[概率机器实现报告](SECTION3_MACHINE_IMPLEMENTATION_2026-10-22.md)；
数学主链的进度见 [第 3 节进度报告](SECTION3_PROGRESS_REPORT_2026-10-22.md)。
论文各项定理、公式及符号的 Lean 对应见 [定理与 Lean term 对应表](SECTION3_LEAN_MAP.md)。

## 形式化约定与本轮结果

用户于 2026-10-22 明确约定：**论文引用的外部定理均可作为显式前提，无须在本仓库重证；
论文内部的数学定理及推导过程必须证明；算法步骤和机器实现可以不形式化；最终结论必须有
Lean 定理。** 这一约定适用于本项目后续工作。算法实现可以省略，不表示最终的 `PP`、
`PSPACE` 结论可以从形式化目标中删除。

数学主链入口为 `import SparseIrred.UpperBounds.PrimeCounting`。
机器实现及新最终定理的直接入口为
`import SparseIrred.UpperBounds.Machine.Conclusion`。用户随后要求继续形式化实际机器，
已构造原论文 **§3.7** 的多项式时间概率机器，并证明其接受概率
正好等于原有数学证明使用的有限接受比例。原先单列的算法实现证书已有构造。
后续指定的三个缺口也已补齐：§3.6 的确定性枚举机器及预处理后核心的线性空间界、
备注 16 的任意固定正间隙，以及命题 13 的一般实数截断。

数学主链已经在
`UniformPrimeIdealEstimate C` 这一显式解析前提下完成：实际因子数域上的引理 3.1 判别式
预算、引理 3.2 的好素数对应、Proposition 4.1 型平均界，以及推论 5.2 的不可约性判据均已
证明。引用的有效素理想计数定理现按上述约定保留为前提，接入其他零点自由仓库或重证该
解析定理不再是本次完成条件。

`UniformPrimeIdealEstimate C` 是显式、对所有数域与截断统一的解析输入。本文自己的
Proposition 4.1 型界没有被当作假设：`integer_prime_root_average_concrete` 从该输入和
已证明的实际引理 3.1、3.2 估计推出真实多项式的平均界。`PrimeCountingDecision` 仍以
平均误差和有理素数计数误差作为接口；`integer_irreducible_iff_primeCounting_threshold_of_uniform_estimate`
已把两项误差估计合并，直接从统一解析输入推出实际截断上的不可约性判据。

该判据已接回原始稀疏项表：`rawList_irreducible_iff_primeCounting_test` 覆盖常数边界、
内容过滤和正次数多项式的计数阈值，`rawList_irreducible_iff_primeCounting_majority` 给出
相应的多数见证形式；`rawList_primeCounting_choice_bits_le` 将多数见证的选择位数界到原始
`encITerms` 编码长度的线性函数。`Section3Arithmetic.lean` 中的
`section3_uniform_arithmetic_conclusion` 将这些结论统一包装：先从外部定理提供的实常数
选择一个固定整数 `C₀`，再对所有原始输入证明判据与位长界。

`Machine/Conclusion.lean` 中的新最终入口为
`section3_irreducibility_mem_PP_and_PSPACE_of_external_theorems`：

```lean
(hExternal : ∃ C : ℝ, 0 < C ∧ EffectivePrimeIdealEstimate (1 / 32) C)
(hAKS : BinaryPrimalityInFP) :
IrredLang ∈ Complexity.PP ∧ IrredLang ∈ Complexity.PSPACE
```

这两个参数均为文献定理输入：统一有效素理想计数估计，以及二进制素性测试属于多项式时间
的 AKS 定理。`BinaryPrimalityInFP` 精确定义为
`binaryPrimeFlag ∈ Complexity.FP`，其中
`binaryPrimeFlag p = [decide (SparseDiv.decNat p).Prime]`。
输入验证、常数和本原性分支、稀疏模幂及导数求值、八模式分支、随机位解析、实际 NTM 构造、
多项式时间界和接受概率等式均已在本仓库证明。

`primeCountingAlgorithmCertificate_of_binaryPrimalityInFP` 从 AKS 前提构造
`PrimeCountingAlgorithmCertificate C₀`。`Section3Conclusion.lean` 中的旧定理
`section3_irreducibility_mem_PP_and_PSPACE` 及原证书接口继续保留，便于已有调用使用；新最终
定理已代入构造出的证书，不再要求调用者额外提供整个不可约性算法的实现或复杂度假设。
本原性过滤和不可约性判据的数学正确性仍由已证明的内部推导提供。

§3.7 的上述入口继续通过已证明的 `PP ⊆ PSPACE` 得到第二个成员资格。
§3.6 另有确定性枚举实现：全输入路线的 `section3_deterministic_streaming_mem_PSPACE`
位于 `Machine/StreamingTrace.lean`，证明实际语言的
`PSPACE` 成员资格；`Machine/StreamingLinearCore.lean` 中的
`section3_linear_streaming_core` 则证明规范、本原、正次数输入上的实际二进制枚举核心，
包括全部运行前缀的 `O(L)` 决策空间和最终输出。该核心自行实现试除判素、模运算、项表解析、
普通及导数求值和 `2A<3P` 比较，不使用 AKS。全输入路线的 `FP` 步骤仍显式使用外部 AKS；
两个入口的前提见完成报告。

备注 16 的新入口为
`SparseIrred.UpperBounds.GeneralGap.section3_irreducibility_mem_PP_and_PSPACE_of_positive_gap`，
位于 `Machine/GeneralGapConclusion.lean`。对每个固定 `δ>0`，先统一选出整数 `r,C₀≥1`，
再使用 `m=128*r*cutoffLog C₀ (r*n) Δ`。已证明
`m≤128*r*(38+clog₂C₀+2*clog₂r)+768*r*L`、四分之一误差、严格多数判据及实际概率机器；
最终只要求该 `δ` 的外部有效计数估计和 AKS。

命题 13 的实数截断入口为 `integer_prime_root_average_concrete_real`
（`RealCutoff.lean`），量化任意 `X : ℝ`、`2<X`。真实根计数、素数计数与素理想计数通过
`⌊X⌋₊` 定义，并已证明与“范数或素数不超过 X”的集合语义一致。
这里使用文献计数定理的原有实数范围接口 `EffectivePrimeIdealEstimateReal`；
`effectivePrimeIdealEstimateReal_to_integer` 证明它限制到整数时得到旧接口。

## 与独立版本的逐项对应

| 独立版本 | 文件／主要定理 | 已证明的范围 |
|---|---|---|
| §1：原始输入的 `log(n+2), log(S+2)=O(L)` | `SparseInputBounds.lean`、`RawInputBounds.lean` | 对实际的 `encITerms` 二进制编码证明度与系数和的界。`raw_input_log_bounds` 适用于未正规化列表，允许重复指数、零系数和抵消。 |
| 引理 3.1：Mahler 测度部分 | `IntegerMahlerBounds.lean` | 实际整数因子 `g∣f` 满足 `1≤M(g)≤M(f)≤S`，并得到对数及系数界。没有把这些结论作为假设。 |
| 引理 3.1：判别式的加权数值汇总 | `WeightedDiscriminantBounds.lean`、`PrimeAverageInstantiation.lean` | 对实际非首一因子的生成数域，证明数域判别式整除整系数正规化判别式，再用 Mahler/Vandermonde 界得到逐域对数判别式界，并对真实因子族推出 `∑wᵢlogDᵢ≤n²Δ`。 |
| 引理 3.1：异常素数数目 | `ExceptionalPrimeCount.lean`、`VandermondeDiscriminant.lean`、`PrimeAverageInstantiation.lean` | 对平方自由因子乘积的实际异常整数 `Z=lc(F)Disc(F)`，证明非零性、大小界及其不同素因子数界，得到异常集合基数 `≤2nΔ`。 |
| 引理 3.2：实际好素数对应 | `PrimeAverageInstantiation.lean`、`GoodReductionRoots.lean`、`DegreeOneCounting.lean` | 对实际整数因子证明：异常集合外的根权重等于各生成数域中次数一素理想的加权贡献，并证明在截断内交换求和。 |
| 命题 4.1、式 (19)、(20) | `PrimeAverage.lean`、`PrimeAverageInstantiation.lean` | 抽象有限族的求和界已实例化为输入多项式的真实整数因子、实际生成数域和实际异常集合。`integer_prime_root_average_concrete` 现仅以统一外部素理想估计为解析前提，推出论文的 `64/4` 全局界。 |
| 引理 5.1：式 (22)--(25) | `CutoffError.lean` | 保留论文常数。实际证明对数积分下界、由素数计数误差推出式 (23)，并从原始全局误差推出四分之一比例误差。三项误差之和 `≤3/64<1/4`。 |
| 引理 5.1：截断的位长 | `inputCutoffExponent_le_raw_length`、`inputCutoff_size_le_raw_length` | 截断参数与原始列表编码相连；具体有 `m≤128(38+clog₂C₀)+768L`、`size(X)≤m+1`。固定 `C₀` 时均为线性界。 |
| 推论 5.2：精确决定不等式 | `PrimeCountingDecision.lean`、`PrimeAverageInstantiation.lean` | `integer_irreducible_iff_primeCounting_threshold_of_uniform_estimate` 从单一统一素理想估计推出实际截断上的 `Irreducible f ↔ 2A<3P`。该数学判据不等于 PP/PSPACE 机器及其资源界证明。 |
| 原始输入上的第 3 节判据 | `RawPrimeCountingDecision.lean`、`Section3Arithmetic.lean` | 对任意 `ITerms` 接回常数边界、本原性条件、计数阈值与多数见证，并证明选择位数线性有界；统一主定理在量化所有输入之前选择 `C₀`。 |
| §6：`p≤X` 与 `p<X` 的衔接 | `PrimeCutoffCounts.lean` | 证明实际截断是合数，严格计数与 mathlib 的 `Nat.primeCounting` 相等，根计数也不受端点影响。 |
| §6：有限循环的正确性 | `PrimeStreaming.lean` | 实现尾递归的素数候选和剩余类扫描；`primeStreaming_eq_counts` 证明结果就是 `(P,A)`，并证明内外循环每个前缀的计数范围。 |
| §6：计数器位长 | `PrimeStreamingBits.lean`、`RawInputBounds.lean` | 所有完整外循环前缀以及内循环更新中的计数器均有位长界；`raw_inputCutoff_counter_bits` 将两个外循环计数器界到原始输入的 `768L`、`769L` 加固定常数。 |
| §6：稀疏模幂及导数求值 | `SparseModularEval.lean` | 定义二分模幂与尾递归稀疏求值，证明等于多项式求值；导数跳过零指数，处理 `a=0`。`sparseModularRootScan_count` 将实际稀疏局部循环接到 `primeRootWeight`。 |
| §7：实际见证的计数 | `PrimeWitnessCount.lean` | 对真正的 `Fin X × Fin X × Bool` 见证，证明 `#R⁺=P`、`#R⁻=A`，使用剩余类的显式枚举对应，没有假设这两个计数等式。 |
| §7：二进制分支数与多数阈值 | `primeWitness_choice_count`、`primeWitness_binary_majority_iff` | 总选择数为 `2^(2m+5)`，严格接受多数当且仅当 `2A<3P`；`primeCounting_choice_bits_le` 证明所需选择位数线性有界。下列机器模块把该有限计数接到真实随机分支。 |
| §7：输入检查及每条分支的多项式时间 | `Machine/CodeValidation.lean`、`CutoffParameters.lean`、`ModularVerifier.lean`、`WitnessFP.lean`、`EncodedVerifierFP.lean` | 验证规范编码，计算截断宽度，处理带符号素数常数和本原性，再执行实际二进制模幂、稀疏求值、导数及八模式选择。通过 Cobham 的已证机器编译结果取得 `FP`；仅判素使用外部 AKS。 |
| §7：实际随机位与见证对应 | `Machine/SeedEncoding.lean`、`SeedPadding.lean`、`RandomSeedVerifier.lean`、`SeedAcceptance.lean` | 显式按 `3,m,m,1,1` 位解析随机串，证明其与见证域双射、忽略后缀保持概率，以及实际字符串验证器的精确接受概率。 |
| §7：真实概率机器及运行时间 | `Machine/PaddedVerifier.lean`、`GuessFixed.lean`、`GuessVerify.lean`、`GuessMachine.lean`、`Precompose.lean` | 构造随机猜测、确定性验证及预处理复合的 NTM；证明所有路径在统一多项式时限内停机，并证明接受概率为 `primeCountingAcceptance C₀ x`。 |
| 原实现证书的构造 | `Machine/Conclusion.lean`、`primeCountingAlgorithmCertificate_of_binaryPrimalityInFP` | 从外部二进制 AKS 定理构造旧的实现接口；接口不再是新最终定理的额外前提。 |
| 最终的整数语言 `PP`、`PSPACE` 结论 | `Machine/Conclusion.lean`、`section3_irreducibility_mem_PP_and_PSPACE_of_external_theorems` | 仅保留统一解析估计和 AKS 两项文献输入，证明实际规范编码语言的成员资格；`PSPACE` 使用已证明的 `PP ⊆ PSPACE`。 |

前一轮已完成的局部根界、重复因子统计量和好约化处的带权根公式继续复用。

## 当前前提与形式化边界

1. **外部解析定理。** 外部有效计数定理的结论写为
   `∃ C : ℝ, 0 < C ∧ EffectivePrimeIdealEstimate (1 / 32) C`。
   `exists_integer_uniform_primeIdeal_estimate` 证明可先选一个统一整数 `C₀ ≥ 1`，再用于
   所有数域、截断和输入多项式。无需在本仓库重证被引用的零点自由及有效计数定理。
2. **引理 3.1 和 3.2 的数域算术部分。** 已完成：Vandermonde 判别式界、非首一因子
   整数正规化及判别式转换、数域判别式整除正规化判别式、实际异常整数非零性与大小界，
   以及好素数根和次数一次素理想的对应。相关结论见
   `integerFactorRootField_logDiscriminant_le`、
   `integerFactorIndex_weighted_fieldLogDiscriminant_le`、
   `integerSquarefreeExceptionalPrimes_card_le` 和
   `integerFactorization_good_prime_root_weight_eq_degreeOne`。
3. **从外部解析估计接到最终截断。** Proposition 4.1 型实际平均界和推论 5.2 的
   不可约性判据均已从 `UniformPrimeIdealEstimate C` 推出。本文内部的平均界和判据没有
   作为外部前提。
4. **外部判素定理与实际机器。** 原论文 §3.7 引用 **[1] Agrawal–Kayal–Saxena,
   “PRIMES is in P”**（独立版本 §7 的 **[5]**）作为精确的 `BinaryPrimalityInFP` 输入。
   AKS 算法本身不在本项目重证。除这一被引用的子程序定理外，完整字符串验证器的组合、
   实际随机 NTM、全路径多项式时间及有限见证概率对应均已证明。
5. **最终复杂性结论与一般间隙。** 原论文第 3 节的固定间隙和备注 16 的任意固定
   `δ>0` 均有实际机器支持的 `PP`、`PSPACE` 定理。§3.6 还给出独立的确定性枚举实现，
   以及预处理后实际核心的全前缀线性决策空间。
6. **覆盖范围。** 命题 13 已覆盖任意实数 `X>2`；文献前提在实数与整数上的接口分别列明。
   第 4 节与独立稿扩展不属于本次完成范围。

`primeStreaming` 等早期接口保留抽象数学定义。§3.6 的新机器通过具体二进制寄存器、
磁带转移及计数等式连接这些定义；§3.7 的字符串程序、随机机器及接受概率对应继续保留。

## 外部文献核对

已再次查看 [DedekindZetaZeroFree](https://github.com/AxiomMath/DedekindZetaZeroFree)
及 [Frei--Sofos--Widmer 的定理 1.1](https://arxiv.org/html/2610.18491v2)。后者明确将
`Li(X)` 定义为 `∫₂ˣ dt/log(t)`，与 `CutoffError` 使用的积分相同；这里没有遗漏
一个对数积分归一化的常数差。对该文书面定理的核对不构成在本仓库中对它的 Lean 证明。

## 检查

```sh
lake build
lake env lean scripts/Axioms.lean
lake env lean scripts/DepAudit.lean
scripts/check_vendor.sh
git diff --check
```

最新完整构建与审计记录见
[第 3 节完成报告](SECTION3_COMPLETION_2026-10-22.md)，汇总公理和传递依赖报告见
`AXIOMS.txt`、`DEP_AUDIT.txt`。机器构造使用的外部解析定理和 AKS 均为显式参数；
审计认证相应条件定理的证明及依赖闭包，不证明这些文献参数本身。
