# 第 4 节完整二进制实现与机器认证

范围：原论文 `1021-AI4Math_Irreducibility.pdf` 第 4 节。接续
[2026-10-22 数学形式化报告](SECTION4_FORMALIZATION_2026-10-22.md)，补齐用户随后明确要求的
低层二进制实现、实现验证及通用条目 oracle 协程的实际图灵机编译。

## 定理 18：实现接口已消去

`SparseIrred.UpperBounds.Section4.BinaryConclusion` 提供：

```lean
section4_irreducibility_mem_PSPACE_unconditional :
  UniformIrredLang ∈ Complexity.PSPACE
```

该定理没有外部数学参数，也没有算法实现参数。
`section4_complete_machine` 给出同一个确定性多带图灵机和固定空间多项式，证明对每个
原始二进制输入：

- 每一个可达机器配置均满足多项式决策空间界。
- 机器终止，输出 `uniformDecision` 的正确判定位。
- 输入特征与扩张次数均可变化，非法编码、非法域头及非法系数向量均拒绝。

具体二进制单步函数是 `section4BinaryStep`。`section4BinaryStep_mem_FP` 证明它属于
complexitylib 的 `FP`；`section4BinaryStep_realization` 用全部已证明的二进制组件构造
原先保留的 `UniformLocalStepRealization`。旧条件式定理为兼容保留，新增最终入口直接使用
已经构造的实例，不再要求用户提供该接口。

统一入口仍为：

```lean
import SparseIrred.UpperBounds.Section4Complete
```

## 二进制组件及其证明

下表路径均相对于 `SparseIrred/UpperBounds/Section4/`。

| 组件 | 主要文件 | 认证内容 |
|---|---|---|
| 参数化的有界列表扫描 | `BinaryList.lean` | 从原始字符串读取、计数、索引和规范化 framed 列表；全输入 Cobham 证明。 |
| 栈的一次实际操作 | `BinaryStack.lean` | 二进制 push/pop、挂起右分支、保存左值、合并结果；`binaryStackStep_correct` 精确对应数学栈的一步。 |
| 域标量与布尔标记 | `BinaryDecision.lean` | 实际加乘、OR、AND 和非零测试的编码分派。 |
| 素域运算 | `BinaryFieldPrime.lean`、`BinaryFieldPrimeCanonical.lean` | 二进制约简、加减乘、幂和逆；精确对应 `ZMod p` 的规范值。 |
| 扩张域运算 | `BinaryFieldVector.lean`、`BinaryFieldShift.lean`、`BinaryFieldMul.lean`、`BinaryFieldPow.lean`、`BinaryField.lean` | 固定长度系数向量；Horner 乘法和归约；二进制幂及逆；域基数 `p^d`；精确对应实际商域。 |
| 原始输入处理 | `BinaryInput.lean`、`BinaryInputView.lean`、`BinaryInputValidation.lean` | 重新编码核查、结构校验、规范系数长度与数字范围检查。 |
| 主多项式系数查询 | `BinarySparse.lean` | 扫描所有项并合并同指数贡献；允许非规范长度的系数向量先归约。 |
| 主多项式次数及导数 | `BinaryDegree.lean`、`BinarySparseMetadata.lean` | 从实际非零系数计算次数，包括重复指数抵消；计算导数系数、导数次数和首项系数的逆。 |
| 域头多项式元数据 | `BinaryPrimePolynomial.lean` | 素域上的稠密系数查询、导数查询及次数扫描，不预设域头不可约。 |
| 矩阵条目 | `BinaryMatrixEntries.lean` | Sylvester 和伴随矩阵的实际二进制下标计算；仅调用已验证的系数和域算术。 |
| 完整地址指令 | `BinaryAddress*.lean` | 矩阵幂、Berkowitz 因子、连乘、Frobenius、删除行列、所有子式及布尔判据的全部指令分派。 |
| 第一阶段 | `BinaryFirstStage.lean`、`BinaryFirstStageRealization.lean` | 实际试除与输入预检的完整二进制实现。 |
| 第二阶段 | `BinaryPrimeStage.lean` | 在已验证的素域上判断模多项式不可约。 |
| 第三阶段 | `BinaryExtensionStage.lean` | 在已验证的扩张域上判断稀疏多项式不可约。 |
| 阶段控制和总程序 | `BinaryControl.lean`、`BinaryConclusion.lean` | 固定二进制转移、各阶段模拟律、完整 `FP` 证明及无实现前提的 `PSPACE`／机器存在性定理。 |

Cobham 证明对所有原始字符串成立，不能通过先固定某个输入、某个特征或某个扩张域后
再提供单独机器来替代均匀性。数学模拟律则证明规范编码上的每个指令、每次算术及
每个状态转移都与既有数学程序一致。

## 通用 oracle 的实际机器编译

条目 oracle 可以运行指数时间。它的原有条件是实际图灵机终止、返回指定矩阵条目，且
所有可达配置满足空间界；没有要求完整条目查询属于 `FP`。

完整包装为 `OracleMachineLemma17.lean` 中的 `lemma17_uniform_scalar_machine`。
给定同一个条目计算机器 `M` 及其 `MatrixEntryMachine M A space` 证明，构造同一个
行列式机器，对每个有效的矩阵描述输入输出完整的 `det A` 域元素编码，并证明所有可达
配置满足固定多项式空间界。矩阵维数、特征、扩张模多项式和原始矩阵描述均是输入数据。

`MatrixEntryMachine` 的两项条件只有条目机器本身的空间界与正确输出／停机性质；
控制器的四个局部操作、初始化、停机检测和完整输出发布都已有实际程序与证明，
不再作为调用者提供的实现接口。

这里准确采用库的 `WithinDecisionSpace` 配置模型：工作带头位置受 `S` 限制，输入头
不超过查询长度加 `S+1`，输出头不超过 `S+1`。因此条目 oracle 的完整配置有有限空间
窗口。本包装接受这一明确的机器契约；不把它直接等同于库中仅约束辅助空间、允许
单向输出头继续空走的所有 `ComputesInSpace` 见证。

引理17只对有效有限域矩阵描述提出计算要求，形式化中对应 `OracleMatrixInputValid`。
它是该引理的输入领域条件，机器不调用不可计算的“有效性 oracle”。定理18的最终机器
则对所有原始字符串成立，并已实现完整输入验证。

- `OracleMachineTM.lean` 对真实图灵机的初始化、一次配置转移、停机检测和完整输出读取
  给出二进制程序及 `FP` 证明。
- `OracleMachineRun.lean` 用“首停之前配置不重复”和有限配置计数，从终止与空间界推出
  指数首停时限；时间界不是额外 oracle 前提。
- `OracleMachineSource.lean` 将实际条目机器连接到已验证的数学协程。
- `OracleMachineDispatch.lean`、`OracleMachineControl.lean`、`OracleMachineLoop.lean`
  实现保存续延、启动查询、逐步推进 oracle、读取返回值及恢复主栈。
- `OracleMachineCompiler.lean` 给出判定型编译；`OracleMachineValue*.lean`、
  `OracleMachinePublish.lean` 和 `OracleMachineScalarCompiler.lean` 给出完整字符串输出。
  输出尾程序是实际 TM 转移逐位复制，包含空串；输出不限于一个判定位。

其中 `OracleScalarCompilerLaws.machine_exists_of_window` 证明真实机器返回整个标量编码，
并在每个运行前缀使用多项式空间。该版本由空间窗口内部推出 oracle 的时限，不接收额外
时间界。其局部控制器方程是通用编译正确性定理的参数；引理 17 的具体包装使用实际
Berkowitz 控制器的已证明实例。

数学协程的编码空间仍具有“控制栈加 oracle 工作区”的加性界。通用低层模拟的物理空间
界允许在这一总宽度上取多项式；原引理 17 本来要求 `S = poly(L)`，因此足以得到其
多项式空间结论。

## 检查状态

定理 18 的无条件机器认证和引理 17 的具体统一机器包装均已构建及独立审阅通过。
第 4 节目录现在包含 105 个已编译模块，本次补入 56 个二进制实现／机器编译模块。

| 检查 | 最终结果 |
|---|---|
| `lake build` | 通过，9468 项构建任务。 |
| `lake env lean scripts/Axioms.lean` | 479 项声明全部通过，结果存于 `docs/AXIOMS.txt`。 |
| `lake env lean scripts/DepAudit.lean` | 463 个入口到达 84,756 个常量；只包含 `propext`、`Quot.sound`、`Classical.choice`。 |
| 未证明项和绕过内核机制扫描 | `SparseIrred/` 无 `sorry`、`admit`、自定义 `axiom`、`native_decide`、`implemented_by`、`extern` 或 `unsafe`。 |
| 全部第 4 节模块 | 105 个源文件均有最新 `.olean`，没有被总入口遗漏的未编译文件。 |
| `scripts/check_vendor.sh` | 全部 38 个 vendored 模块与原固定提交完全相同。 |
| `git diff --check` | 通过。 |

第 4 节最终语言定理和完整判定机器不再保留实现接口。引理 17 的条目机器条件是其明确
输入假设，准确的空间模型已在上节列出；这些条件没有被当成全行列式程序的实现假设。

实际运行 `section4BinaryStep` 的七项完整二进制程序测试已全部通过：

| 输入 | 结果 |
|---|---|
| `F₂` 上 `X+1` | 接受 |
| `F₂` 上两项 `X+X`，相加后为零 | 拒绝 |
| `F₂` 上 `X²+X+1` | 接受 |
| `F₂` 上 `X²+1`，导数为零且有重因子 | 拒绝 |
| `F₄ = F₂[t]/(t²+t+1)` 上 `X+t` | 接受 |
| 将合数 `4` 写入特征字段 | 拒绝 |
| 空原始输入 | 拒绝 |

这些执行检查补充内核证明；它们执行的是已认证的二进制状态程序，未用测试替代实际
图灵机的通用正确性与空间证明。

可用 `lake env lean scripts/Section4Smoke.lean` 重现，预期依次输出
`some [true]`、`some [false]`、`some [true]`、`some [false]`、`some [true]`、
`some [false]`、`some [false]`，全部应在给定 fuel 内完成。
