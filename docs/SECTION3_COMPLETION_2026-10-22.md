# 原论文第 3 节：剩余三项的补全

范围：`1021-AI4Math_Irreducibility.pdf` 第 3 节，仅核对该版本的编号和结论。
本文接续此前的 §3.7 机器实现报告。统一导入入口：

```lean
import SparseIrred.UpperBounds.Section3Complete
```

原有 `import SparseIrred` 和 `import SparseIrred.UpperBounds.PrimeCounting` 也包含新入口。

## 1. §3.6 的确定性算法

确定性枚举已有两层实际机器证明，二者都使用明确的图灵机模型。

| 证明层次 | 主要入口 | 精确范围 |
|---|---|---|
| 全输入编码、边界情况及多项式空间 | `Machine.section3_deterministic_streaming_mem_PSPACE` | 从初始输入配置执行确定性枚举，覆盖错误编码、常数和非本原输入。通过有界状态迭代构造实际机器，直接证明 `PSPACE`，不调用 `PP ⊆ PSPACE`。这一版本用引用的 AKS 定理证明单步字符串函数属于 `FP`。 |
| 预处理后的枚举核心及线性空间 | `Machine.section3_linear_streaming_core` | 对规范、本原、正次数输入，从明确的预加载磁带配置 `section3CoreStart` 执行。实际机器自行试除判素，解析稀疏项、模求值、检测重根、累计两个计数器并输出判定位；所有可达配置满足 `A*L+B` 决策空间界。此核心不使用 AKS。 |

下文的 `Machine.` 均指 `SparseIrred.UpperBounds.Machine.`。

全输入的多项式空间定理和预处理后核心的线性空间定理是两个明确的接口；没有把
后者的预加载配置说成原始输入的 `TM.initCfg`。输入装载本身有实际三状态转导机
`packedInputTM`，在 `|x|+2` 步内输出 `x ++ [true]`，并证明所有可达配置的线性辅助空间界。
截断和编码检查复用已有的已验证多项式时间预处理。

### 枚举与论文的对应

程序使用矩形枚举 `0 ≤ p,a < X`。非素数行以及 `a ≥ p` 的位置贡献零；每个素数行
只在 `a=0` 时将 `P` 加一。`streamCounts_eq_counts` 和
`coreEnumeration_eq_paper_counts` 证明，这与正文的 `2 ≤ p < X, 0 ≤ a < p` 枚举有
相同的两个最终计数器。插入的无贡献位置不改变判据或空间界。

真正的二进制循环由 `BinaryRoutine.binaryFor` 编译为图灵机，循环次数存放在二进制
寄存器中；不会为指数级循环生成一元计数器或指数级状态空间。

核心固定使用 70 个二进制寄存器，最后六个保存：输入、截断、素数候选、剩余类候选、
`P`、`A`。每一格执行后清理前 64 个工作寄存器，供下一格复用。

### 已证明的低层组件

| 功能 | 主要 Lean term |
|---|---|
| 试除判素，含 `0,1` | `binaryPrime_sound`、`binaryPrime_flag_iff`、`binaryPrime_space` |
| 模运算、模幂与单项求值 | `framedMod_sound`、`binaryPow_effect`、`binaryTerm_effect` 及相应空间定理 |
| 逐位读取及成帧项解析 | `inputReadBit_effect`、`frameInput_effect`、`parseTerm70_spec` |
| 去掉保留末尾零位的哨兵 | `unpackInput_effect`、`unpackInput_space` |
| 带符号普通／导数求值 | `binarySparseEval_zero_iff`、`binarySparseEval_space` |
| 一格的计数增量 | `completeCell_effect`、`completeCellSpec` |
| 完整双循环 | `coreEnumeration_sound`、`coreEnumeration_effect`、`coreEnumeration_space` |
| 实际输出 `2A<3P` | `coreVerdict_emitted` |
| 核心最终输出及线性空间 | `section3BinaryCore_emitted`、`section3BinaryCore_space_linear` |

模幂和试除允许较长运行时间。它们的空间证明控制所有中间寄存器及真实磁带运行前缀，
而非把时间界误作线性空间界。普通求值和导数求值都按稀疏项读取，正、负系数分别模累加，
不生成稠密系数向量。

线性空间核心的模幂采用按指数值重复乘模的二进制计数循环。它的计算值和线性空间界已证明，
但没有为这一核心声称多项式运行时间；§3.7 的多项式时间验证器继续使用已有二分模幂实现。

`branchZeroSelected` 复用同一真实条件分支机器，并证明只按实际执行分支计量空间的
Hoare 契约。该改进用于避开已经结束时根本不会执行的解析分支；没有假设无效输入满足
解析器的前置条件。

`binaryRoutine_bit_decisionSpace` 还将空间控制扩展到输出磁带：利用真实机器输出头
不左移、最终只输出一位，证明所有运行前缀的输出头也在界内。因此最终定理使用的是
`Cfg.WithinDecisionSpace`。

## 2. 备注 16：任意固定正间隙

新的完整最终入口：

```lean
SparseIrred.UpperBounds.GeneralGap.
  section3_irreducibility_mem_PP_and_PSPACE_of_positive_gap
```

其参数为任意固定 `δ : ℝ`、`0 < δ`，以及

```lean
∃ C : ℝ, 0 < C ∧ EffectivePrimeIdealEstimate δ C
```

和引用的 `BinaryPrimalityInFP`。结论仍为规范稀疏整数不可约性语言属于 `PP` 和
`PSPACE`，不再要求 `δ=1/32`，也没有算法实现证书参数。

证明先选与输入无关的整数 `r≥1`，使 `1≤32*r*δ`，并选统一整数计数常数 `C₀`。
新截断为

```text
m = 128*r*cutoffLog C₀ (r*n) Δ,
X = 2^m.
```

全局平均误差、素数计数下界、严格四分之一误差、不可约性阈值、线性随机位界和实际
概率机器均已推广。固定 `δ` 只改变机器常数；没有把随输入缩小的间隙纳入结论。

## 3. 命题 13：任意实数截断

`RealCutoff.lean` 用向下取整定义真实有限计数，并证明成员关系精确对应
`p ≤ X` 和 `N(𝔭) ≤ X`。主入口为

```lean
SparseIrred.UpperBounds.integer_prime_root_average_concrete_real
```

它覆盖所有实数 `X>2`，包括 `2<X<3`，保留正文的 `64/4` 常数。内部根数与数域计数
比较在整数下取整处进行，解析估计则直接在真实的实数 `X` 处使用，从而不会遗漏
`Li(X)` 与 `Li(⌊X⌋)` 的差。

`RealCutoffGeneralGap.lean` 的
`integer_prime_root_average_concrete_real_of_gap` 进一步同时覆盖任意固定 `δ>0` 和
任意实数 `X>2`。一般间隙下的系数为 `2*δ⁻¹` 和 `4`；`δ=1/32` 时即正文系数。

实数外部计数接口 `EffectivePrimeIdealEstimateReal` 是同一文献计数定理的实数版本。
`effectivePrimeIdealEstimateReal_to_integer` 证明其推出旧整数接口。命题 13 的内部
平均估计没有被作为外部前提。

## 4. 保留的外部输入与验证

允许的外部输入仍是原论文 §3.1 的文献计数估计，以及使用多项式时间判素的接口中
§3.7 引用的 AKS 定理。试除及线性空间核心自身不依赖 AKS。没有新增自定义全局公理、
`sorry` 或未证明的算法实现接口。

最终验证已完成：

| 检查 | 结果 |
|---|---|
| `lake build` | 通过，9351 个构建任务 |
| `lake env lean scripts/Axioms.lean` | 370 个声明全部通过；仅 `propext`、`Classical.choice`、`Quot.sound` |
| `lake env lean scripts/DepAudit.lean` | 354 个入口，81,884 个传递常量；仅上述标准公理 |
| 新增源代码占位及自定义公理检查 | 无 `sorry`、`admit`、自定义公理或不可信计算替代 |
| `scripts/check_vendor.sh` | 38 个 vendored 模块与原提交一致 |
| `git diff --check` | 通过 |

审计原始结果见 [AXIOMS.txt](AXIOMS.txt) 和 [DEP_AUDIT.txt](DEP_AUDIT.txt)。这些数字是
整个项目的构建和审计规模，不是第 3 节独立定理数或完成百分比。
