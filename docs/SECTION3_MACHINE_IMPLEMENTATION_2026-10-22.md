# 第 3.7 节实际机器实现与 Lean 对应（2026-10-22）

> 本文保留 §3.7 概率机器完成时的实现细节和当时的构建统计。
> 后续原论文 §3.6 的确定性枚举机器、预处理后核心的线性决策空间、备注 16 的任意固定正间隙、
> 命题 13 的实数截断均见 [第 3 节最新完成报告](SECTION3_COMPLETION_2026-10-22.md)。
> 当前对应表见 [SECTION3_LEAN_MAP.md](SECTION3_LEAN_MAP.md) 的 §2.7–2.8。

本报告记录在此前第 3 节数学主链完成之后，进一步实现论文 §3.7 概率机器的工作。
论文来源为根目录 `1021-AI4Math_Irreducibility.pdf`；其 §3.7 对应独立稿
`sparse_irreducibility_complete_qrh.pdf` 的 §7。§3.6 是确定性空间枚举算法，
不属于本报告所构造的概率机器。

**完成状态：实际概率机器、所有路径的多项式时间界、精确接受概率和新最终定理均已完成，
完整构建与公理审计通过。**
最终入口为 `section3_irreducibility_mem_PP_and_PSPACE_of_external_theorems`，
只接收外部有效计数前提与 AKS 前提。最终检查结果见第 6 节。

## 1. 实现对象与外部输入

算法输入是规范稀疏整数多项式的二进制编码 `x : List Bool`。机器处理以下全部情况：

1. 编码无法解析、整数编码不规范或稀疏项表不规范：拒绝。
2. 常数多项式：其常数系数的绝对值是素数时接受；因此 `±p` 接受，零、单位和合数常数拒绝。
3. 正次数而非本原的多项式：拒绝。
4. 正次数本原多项式：执行论文的正负见证和八模式多数判定。

`PrimeCountingAlgorithmCertificate C₀` 是此前为了允许省略算法而设置的接口。
本轮通过 `primeCountingAlgorithmCertificate_of_binaryPrimalityInFP` 从实际程序、
机器组合和资源界**证明这个接口的存在性**，再代入已有数学正确性定理。
它没有作为新最终定理需要用户提供的算法假设。

本轮机器层保留的文献前提是：

```lean
SparseIrred.UpperBounds.BinaryPrimalityInFP
```

其定义为 `binaryPrimeFlag ∈ Complexity.FP`，其中
`binaryPrimeFlag p = [decide (decNat p).Prime]`。这准确表达“二进制素性测试属于多项式时间”。
它对应 **Agrawal–Kayal–Saxena，*PRIMES is in P*，Annals of Mathematics 160 (2004),
781–793**，原论文 **[1]、§3.7**，独立稿 **[5]、§7**。

这里使用 AKS 的外部复杂性定理来提供素性测试机器及其多项式时间界；并没有把整个
不可约性验证器、其正确性或其资源界作为外部前提。`decide Nat.Prime` 给出可执行的
函数定义，也不等于已经证明该默认判定实现具有 AKS 的时间界；二者通过同一个函数的
`FP` 规格连接。

另一个外部输入属于解析数学层，与 AKS 独立：

```lean
∃ C : ℝ, 0 < C ∧ EffectivePrimeIdealEstimate (1 / 32) C
```

它汇总原论文 **[6]** 的固定零点自由间隙与 **[9]** 的统一有效素理想计数结果，位置为
§3.1、式 (22)–(23)。具体书目信息见
[此前进度报告的外部文献表](SECTION3_PROGRESS_REPORT_2026-10-22.md#41-外部文献前提)。
解析前提用于证明所选截断上的多数判据正确；AKS 前提用于证明每条计算路径的运行时间。

## 2. 一条计算路径做什么

对合法输入计算论文的截断指数 `m`，取 `X = 2^m`。随机串按以下顺序切分：

| 字段 | 位数 | 用途 |
|---|---:|---|
| `mode` | 3 | 在 8 种模式中等概率选择 |
| `p` | `m` | 素数候选，范围为 `0 ≤ p < X` |
| `a` | `m` | 剩余类候选，负见证还会检查 `a < p` |
| `b` | 1 | 区分普通根与重根的额外见证 |
| `coin` | 1 | 无见证时保持接受、拒绝各半 |

总计 `q = 2m+5` 个随机位。字符串实现 `randomSeedVerifier C₀ x seed` 从输入实际计算
字段宽度，执行切片，再调用 `encodedVerifierStr`。并非把随机串到见证的对应作为假设：
`seedPrimeChoices_bijective` 证明固定长度随机串与
`Fin 8 × PrimeWitness (2^m) × Bool` 之间为双射。

稀疏模求值按项处理二进制指数，通过模幂计算每一项；导数计算对零指数单独处理，避免
减一边界错误。其值与 `((toPolyZ l).map (Int.castRingHom (ZMod p))).eval a` 以及对应的
导数求值相等。局部求值的正确性允许重复指数、零系数和相消；完整语言解码则检查规范
编码后才进入判定分支。

此前已证明的见证计数在实际字符串程序上继续成立：正见证数为 `P`，负见证数为 `A`；
前三种模式给每个正见证贡献 `+6`，接着两种模式给每个负见证贡献 `−4`，其余模式的
净贡献为零。因此接受路径数减去拒绝路径数为 `2(3P−2A)`。

## 3. 从字符串程序到实际 Turing 机器

字符串程序用 complexitylib 的 **Cobham 函数代数**组合。每个内部函数的封闭性证明
连接到库中已证明的 `FP` 机器存在性定理；这里只借用外部的二进制素性测试 `FP` 前提。
`encodedVerifierStr_mem_FPn` 覆盖全部输入预处理和六个显式参数，
`randomSeedVerifier_mem_FP` 进一步覆盖随机串解析。

完整概率机器复用实际的有限控制和磁带操作，依次执行：

1. 构造一元长度计数器。
2. 将输入头移回约定的开始位置。
3. 写入恰好指定数量的随机位，再回卷见证带。
4. 在工作带构造输入与见证的配对编码。
5. 模拟已验证的确定性分支验证器。

`fixedGuessVerifyNTM M` 是 complexitylib 的真实 `NTM (k+3)`，具有有限状态空间、
转移函数和磁带动作。它并非仅以“接受条件”定义的抽象谓词。固定猜测禁用原有有界
猜测器的提前停止选择；随机写位仍然保持公平。

该复用机器在输入 `z` 上猜测 `|z|+1` 位。为保证这个长度覆盖全部 `2m+5` 位，
`padPrimeInput C₀ x` 对原输入作线性填充，并把原输入保存在第一个配对字段中。
`paddedPrimeVerifier` 取回原输入、忽略多余的随机尾部。最后通过实际的确定性预处理与
NTM 组合机器，把填充步骤纳入原始输入 `x` 的执行。

构造在 theorem 层给出机器及其正确性。依赖外部 `FP` 存在性定理时，允许在证明中选择
相应的机器；本轮没有另外输出 AKS 的独立源程序或具体可执行文件。

## 4. 时间界与精确概率

只证明“有足够多的正确见证”不足以证明实际机器属于 `PP`。这里还需要处理行政步骤
消耗的随机选择位，以及不同阶段的运行时限。

设固定猜测器要写 `B` 位。`guessFixedNTM_halts_with_seed` 证明它在 `3B+3` 步内完成，
真正写入的位位于相对时间 `2i+1`。`fixedGuessVerify_setup_uniform` 证明，猜测开始前
存在一个与全部随机选择无关的时间 `t₀` 和配置，且

```text
t₀ ≤ 2 * inputLengthPlusOneCounterTime |z| + 5.
```

因此全局随机写位位置为 `t₀+2i+1`。这些位置互不相同。`card_scheduledSeed_fiber`
证明，给定 `B` 位有效随机串，在总长 `T` 的选择序列中恰有 `2^(T−B)` 个扩展。
行政步骤的额外选择因子在接受比例的分子、分母中精确抵消。

完整猜测验证器使用 `satGuessVerifyTime f`：该时限包含计数器、回卷、猜测、配对，
以及对所有允许的配对输入长度取有限最大值的验证器时间。取最大值使证明无须额外假设
初始时间函数 `f` 单调。`fixedGuessVerifyNTM_polynomial_time` 证明每条路径都在
多项式界内停止；停止后的延长时间不改变配置和接受结果。

确定性填充与概率机器的组合使用时限

```text
4 * TF(n) + 11 + TG(TF(n)),
```

其中以自然系数多项式上界替换需要单调性的时间界。`precompose_acceptProb` 证明该
实际组合保持精确概率，`exists_polynomial_precompose` 同时保留所有路径的停止界和
多项式增长界。

概率衔接分为三个已明确命名的层次：

| 层次 | Lean 入口 | 结论 |
|---|---|---|
| 可执行有限分支 | `executableEncodedAcceptance_eq` | 有限接受比例等于 `primeCountingAcceptance C₀ x` |
| 实际字符串验证器 | `randomSeedVerifier_eventProb`、`paddedPrimeVerifier_eventProb` | 精确长度与填充长度的公平随机串给出相同接受概率 |
| 实际 NTM | `fixedGuessVerifyNTM_acceptProb`、`precompose_acceptProb` | 实际磁带执行、阶段切换和预处理保持上述概率 |

## 5. 模块与主要 Lean term 对应

源码位于 `SparseIrred/UpperBounds/Machine/`。下表按功能顺序列出当前 21 个模块。
统一导入为 `import SparseIrred.UpperBounds.Machine`，也由原有的 `PrimeCounting` 入口导入。

除表中明确说明的少数模块外，命名空间为 `SparseIrred.UpperBounds.Machine`。

| 模块 | 主要 term | 对应作用 |
|---|---|---|
| [Preprocess.lean](../SparseIrred/UpperBounds/Machine/Preprocess.lean) | `decodeTerms`、`decodePoly_eq_map_decodeTerms`、`contentZ_eq_one_iff` | 规范解码、内容与本原性对应 |
| [CodeValidation.lean](../SparseIrred/UpperBounds/Machine/CodeValidation.lean) | `validCode_mem_FP`、`validCode_eq_true_iff` | 规范输入检查的多项式时间与精确语义 |
| [ExecutableWitness.lean](../SparseIrred/UpperBounds/Machine/ExecutableWitness.lean) | `executablePrimeMajority`、`executablePrimeBranch_balance` | 可执行局部见证和八模式计数；命名空间为 `UpperBounds` |
| [ExecutableBranch.lean](../SparseIrred/UpperBounds/Machine/ExecutableBranch.lean) | `executableEncodedDecision`、`executableEncodedAcceptance_eq` | 全部边界分支与原数学接受概率一致 |
| [ModularVerifier.lean](../SparseIrred/UpperBounds/Machine/ModularVerifier.lean) | `sparseEvalModStr_mem_FP`、`sparseEvalModStr_zero_flag` | 稀疏模求值、导数及零判定的字符串复杂度；命名空间为 `UpperBounds` |
| [WitnessFP.lean](../SparseIrred/UpperBounds/Machine/WitnessFP.lean) | `BinaryPrimalityInFP`、`primeMajorityStr_mem_FPn`、`primeMajorityStr_eq` | 仅使用 AKS 前提组合局部见证验证器；命名空间为 `UpperBounds` |
| [EncodedVerifierFP.lean](../SparseIrred/UpperBounds/Machine/EncodedVerifierFP.lean) | `encodedVerifierStr_mem_FPn`、`encodedVerifierStr_eq` | 完整输入检查、常数和内容分支的多项式时间实现 |
| [CutoffParameters.lean](../SparseIrred/UpperBounds/Machine/CutoffParameters.lean) | `cutoffExponentStr_mem_FP`、`cutoffUnary_eq` | 以二进制计算 `Δ,m`，用已证明线性界生成长度标尺 |
| [RandomSeedVerifier.lean](../SparseIrred/UpperBounds/Machine/RandomSeedVerifier.lean) | `randomSeedVerifier_mem_FP`、`randomSeedVerifier_eq` | 平面随机串的字段解析与完整单路径执行 |
| [SeedEncoding.lean](../SparseIrred/UpperBounds/Machine/SeedEncoding.lean) | `seedPrimeChoices_bijective`、`eventProb_seedPrimeChoices` | 固定长度二进制种子与论文有限见证的双射；命名空间为 `UpperBounds` |
| [SeedAcceptance.lean](../SparseIrred/UpperBounds/Machine/SeedAcceptance.lean) | `randomSeedVerifier_eventProb` | 字符串验证器的准确接受比例 |
| [SeedPadding.lean](../SparseIrred/UpperBounds/Machine/SeedPadding.lean) | `eventProb_take_ofFn`、`eventProb_of_suffix_ignored` | 忽略随机尾部不改变分布；命名空间为 `UpperBounds` |
| [PaddedVerifier.lean](../SparseIrred/UpperBounds/Machine/PaddedVerifier.lean) | `padPrimeInput_mem_FP`、`paddedPrimeVerifier_eventProb` | 线性输入填充和较长随机带上的概率保持 |
| [GuessVerify.lean](../SparseIrred/UpperBounds/Machine/GuessVerify.lean) | `card_scheduledSeed_fiber`、`acceptProb_eq_verifier_fraction` | 行政步骤随机位的纤维计数与实际 NTM 概率转移 |
| [GuessFixed.lean](../SparseIrred/UpperBounds/Machine/GuessFixed.lean) | `guessFixedNTM`、`guessFixedNTM_halts_with_exact_tape` | 固定长度公平猜测的实际磁带实现 |
| [GuessPipeline.lean](../SparseIrred/UpperBounds/Machine/GuessPipeline.lean) | `fixedGuessVerifyNTM`、`fixedGuessVerifyNTM_polynomial_time` | 完整五阶段 NTM 与全部路径的多项式停止界 |
| [GuessSetup.lean](../SparseIrred/UpperBounds/Machine/GuessSetup.lean) | `fixedGuessVerify_setup_uniform` | 全部随机路径共用的确定性前缀与猜测入口配置 |
| [GuessTail.lean](../SparseIrred/UpperBounds/Machine/GuessTail.lean) | `fixedGuessVerifyNTM_guess_start_decides` | 从猜测入口，经配对与确定性验证，得到准确输出 |
| [GuessMachine.lean](../SparseIrred/UpperBounds/Machine/GuessMachine.lean) | `fixedGuessVerifyNTM_acceptProb` | 完整 NTM 与均匀随机种子的精确概率等式 |
| [Precompose.lean](../SparseIrred/UpperBounds/Machine/Precompose.lean) | `exists_polynomial_precompose` | 实际确定性预处理与 NTM 的概率和资源界组合 |
| [Conclusion.lean](../SparseIrred/UpperBounds/Machine/Conclusion.lean) | `primeCountingAlgorithmCertificate_of_binaryPrimalityInFP`、`section3_irreducibility_mem_PP_and_PSPACE_of_external_theorems` | 构造原算法证书并消去该前提，得到最终 `PP`、`PSPACE` 结论；命名空间为 `UpperBounds` |

上述 `UpperBounds` 简写均指 `SparseIrred.UpperBounds`，不是额外嵌套于 `Machine` 下。

## 6. 验证与最终合并记录

已单独检查可执行局部和完整分支的边界，包括零、单位、带符号素数常数、合数常数、
非本原输入、非法重复项编码、普通根和重根。`GuessSetup` 的统一前缀证明也已构建。
这些模块的关键定理公理审计只有 `propext`、`Classical.choice`、`Quot.sound`。

本轮最终合并的验证记录如下：

| 检查 | 结果 |
|---|---|
| `lake build` | 通过，9210 个构建任务 |
| `scripts/Axioms.lean` | 267 个声明的 `#print axioms` 检查通过 |
| `scripts/DepAudit.lean` | 251 个唯一入口，传递追踪 79,245 个常量 |
| 全部可达公理 | 仅 `propext`、`Classical.choice`、`Quot.sound` |
| `Machine/` 新模块 | 21 个模块，无 `sorry`、`admit`、自定义公理或 `sorryAx` |
| Vendor 一致性 | 38 个 vendored 模块与原提交一致 |
| `git diff --check` | 通过 |
| 本报告第 7 节 Lean 调用示例 | 编译通过；构造证书和新最终定理的单独公理检查也通过 |

原始输出见 [AXIOMS.txt](AXIOMS.txt) 和 [DEP_AUDIT.txt](DEP_AUDIT.txt)。267、251 是整个
项目的审计入口数，并非第 3.7 节的独立定理数。公理审计确认条件命题及其依赖使用的
公理；它不证明作为显式参数保留的解析计数定理与 AKS 定理。

以上统计对应 §3.7 概率机器完成的历史阶段。当时的 `PSPACE` 入口使用
`PP_subset_PSPACE`；后续 §3.6 的确定性枚举及线性空间核心已另行实现，入口为
`Machine.section3_linear_streaming_core`，详见最新完成报告。
外部计数定理和 AKS 定理继续按约定保留为显式文献前提。

## 7. 新最终定理的精确调用

```lean
import SparseIrred.UpperBounds.Machine

open SparseIrred SparseIrred.UpperBounds

example
    (hExternal : ∃ C : ℝ, 0 < C ∧ EffectivePrimeIdealEstimate (1 / 32) C)
    (hAKS : BinaryPrimalityInFP) :
    IrredLang ∈ Complexity.PP ∧ IrredLang ∈ Complexity.PSPACE :=
  section3_irreducibility_mem_PP_and_PSPACE_of_external_theorems hExternal hAKS
```

若已固定统一整数常数 `C₀ ≥ 1`，入口为
`irreducibility_mem_PP_and_PSPACE_of_external_theorems C₀ hC hExternal hAKS`，其中
`hExternal : UniformPrimeIdealEstimate C₀`。

上述入口内部调用构造定理
`primeCountingAlgorithmCertificate_of_binaryPrimalityInFP C₀ hAKS`。后者对每个自然数
`C₀` 都给出存在实际 NTM、多项式全路径时限与精确接受概率的证书，不要求先证明解析
估计。因此，**机器实现的正确性与时间界不依赖解析猜想；解析输入只用于证明该机器
判定的多数阈值恰好对应不可约性。**
