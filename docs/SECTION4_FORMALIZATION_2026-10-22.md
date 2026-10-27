# 原论文第 4 节形式化

**2026-10-23 更新：** 本报告中的“局部实现接口仍保留”是上一阶段的历史状态。
该接口现已由具体二进制程序构造，无实现参数的最终定理是
`section4_irreducibility_mem_PSPACE_unconditional` 和 `section4_complete_machine`。
后续实现、通用 oracle 编译和最新审计见
[完整机器认证报告](SECTION4_MACHINE_CERTIFICATION_2026-10-23.md)。

对象为 `1021-AI4Math_Irreducibility.pdf` 第 4 节的引理 17、定理 18 和公式 (47)–(49)。
本次不使用独立稿或第 3 节的解析数论前提。

统一导入入口：

```lean
import SparseIrred.UpperBounds.Section4Complete
```

原有 `import SparseIrred` 也包含该入口。

## 结果与前提的读法

有限域输入包含二进制素数特征 `p`、定义扩张的稠密首一模多项式 `h`，以及稀疏多项式的
系数向量和二进制指数。扩张次数和特征均随输入变化，域元素用 `h` 的幂基表示。
输入格式、素性、`h` 的不可约性和系数向量格式都接受检查；非法输入拒绝。
稀疏项允许乱序、重复指数和零系数，解释时相加，不额外要求输入已经正规化。

不带额外前提的数学结果包括：原文全部代数判据、实际地址栈程序的正确性和终止、
输入位数界、全执行前缀的栈深与编码长度界，以及三阶段程序接受当且仅当输入多项式不可约。

最终 complexitylib `PSPACE` 定理保留一个**低层局部实现接口**：要求一个多项式时间的
二进制函数实现已定义的小步转移、初始化和输出。这是范围约定允许省略的机器实现，
不是文献外部定理。接口不假设行列式算法正确、不假设不可约判定正确，也不假设完整程序
属于 `PSPACE`；这些结论由项目内证明推出。域运算、二进制下标算术、稀疏系数查询及
栈的编解码属于该局部实现的内容。

因此，应区分“数学程序与资源推导已经证明”和“低层二进制单步函数的 `FP` 实现已经构造”。
本次按允许省略算法实现的约定保留后者，不将条件式结论表述为无实现前提的完整机器认证。

最终定理在 `Section4/Conclusion.lean`：

```lean
section4_irreducibility_mem_PSPACE
    (h : UniformLocalStepRealization G) : UniformIrredLang ∈ Complexity.PSPACE
```

`section4_machine_exists h` 进一步给出 complexitylib 的确定性多带机器，证明每个可达配置
都位于某个输入长度多项式的空间窗口内，并最终输出 `uniformDecision` 的判定位。
`UniformLocalStepRealization G` 是显式 `Prop`，只含 `G ∈ FP`、初始化方程、单步转移方程和
最终位发布方程；它不包含完整运行的正确性、终止或空间假设。编码固定为 `uniformCode`，
不能通过任意选择过短的编码来隐藏空间消耗。

## 论文与 Lean 对应

下表未标注前缀的 term 位于 `SparseIrred.UpperBounds.Section4`；标注 `UB.` 的位于
`SparseIrred.UpperBounds`。

| 论文内容 | Lean term | 对应模块 |
|---|---|---|
| 形式幂级数逆矩阵 | `berkowitzPencil_mul_resolvent`、`berkowitzResolvent_mul_pencil` | `Section4/Berkowitz.lean` |
| Schur 恒等式及系数比较 | `berkowitz_charpolyRev_series`、`berkowitz_coeff_recurrence` | `Section4/Berkowitz.lean` |
| 式 (47)，`c(H)=T(H)c(M)` | `berkowitz_toeplitz_mulVec`、`berkowitz_head_tail_mulVec` | `Section4/Berkowitz.lean` |
| 补零矩阵 `Q₀…Qₙ₋₁` 连乘 | `berkowitzFactors_prod_mulVec`、`berkowitzFactors_det` | `Section4/BerkowitzProduct.lean` |
| 直接按下标读取 `Q`，不生成整张矩阵或系数向量 | `indexedBerkowitzDeterminant_eq_det` | `Section4/BerkowitzIndexed.lean` |
| 完整 Berkowitz 小步求值程序 | `berkowitzProgram_correct`、`berkowitzProgram_stack_bound` | `Section4/BerkowitzProgram.lean` |
| 引理 17：任意空间受限条目 oracle 的协程组合 | `lemma17_space_composition`、`lemma17_faithful_space_composition` | `Section4/BerkowitzOracleSpace.lean` |
| 非首一输入的正规化 | `UB.monicRepresentative_monic`、`UB.monicRepresentative_irreducible_iff` | `Section4/FactorRankOracle.lean` |
| Sylvester 矩阵系数查询与结式 | `UB.coefficientSylvesterEntry_eq`、`sylvesterProgram_value` | `Section4/FactorRankOracle.lean`、`Section4/PolynomialProgram.lean` |
| 结式平方自由筛选 | `UB.resultant_derivative_ne_zero_iff` | `FiniteFieldCriterion.lean` |
| 式 (48)，`Bᵢⱼ=(C^(qj))ᵢ₀` | `UB.coefficientFrobenius_eq_frobeniusMatrix`、`frobeniusEntryProgram_value` | `Section4/FactorRankOracle.lean`、`Section4/BerkowitzFrobeniusProgram.lean` |
| CRT 分解及因子数等于不动空间维数 | `UB.finrank_frobeniusFixedSpace_eq_distinctFactorCount` | `Section4/FactorRank.lean` |
| 式 (49)，`rank(B−I)=n−r` | `UB.frobeniusMatrix_rank_eq_degree_sub_distinctFactorCount` | `Section4/FactorRank.lean` |
| 不可约性等价于结式非零且存在非零删行删列子式 | `UB.irreducible_iff_coefficient_oracle_tests` | `Section4/FactorRankOracle.lean` |
| 子式内部继续调用伴随矩阵幂程序 | `minorProgram_value`、`minorProgram_stack_bound` | `Section4/BerkowitzFrobeniusProgram.lean` |
| 顺序双计数器子式搜索 | `scanSquare_eq_true_iff`、`coefficientOracleDecision_correct` | `Section4/Decision.lean` |
| 搜索循环终止与所有前缀计数器界 | `scanStep_run`、`scanStep_register_sizes` | `Section4/DecisionScan.lean` |
| 将全部子式检查接入同一地址栈 | `minorSearchProgram_value`、`polynomialProgram_halts_correct` | `Section4/PolynomialProgram.lean` |
| 规范域元素与实际商域的双射 | `FieldCode.elementEquiv`、`FieldCode.element_encodeElement` | `Section4/FieldElements.lean` |
| 输入长度与次数、域大小、`q*j` 位数 | `Input.polynomial_degree_size_le`、`Input.field_card_size_le`、`Input.frobenius_exponent_size_le` | `Section4/InputBounds.lean` |
| 实际标量编码的长度 | `Input.scalar_encoding_length_le` | `Section4/FieldBounds.lean` |
| 域头验证使用同一不可约判定 | `FieldCode.stagedHeaderDecision_correct` | `Section4/HeaderBounds.lean` |
| 试除素性程序，不要求 AKS 前提 | `primeDivisorProgram_value`、`preflightAnswer_correct` | `Section4/PrimalityProgram.lean` |
| 均匀二进制语言 | `UniformIrredLang`、`uniformDecision_correct` | `Section4/Language.lean` |
| 先验证素域，再验证扩张，再判定输入多项式 | `uniformStages_correct` | `Section4/UniformStages.lean` |
| 三阶段的统一栈深与终止时钟 | `uniformStages_work_bound`、`uniformStages_time_budget` | `Section4/UniformStageBounds.lean` |
| 全部控制状态的实际二进制码长 | `uniformCode_length` | `Section4/EntryMachineUniformEncoding.lean` |
| 完整控制状态编码单射 | `uniformCode_injective` | `Section4/EntryMachineUniformFaithful.lean` |
| 定理 18 的最终复杂性结论 | `section4_irreducibility_mem_PSPACE`、`section4_machine_exists` | `Section4/Conclusion.lean` |

最终程序采用论文的 Berkowitz 路线。此前的 Bird 行列式定理仍保留，但不承担此处实际
地址程序的行列式实现。

实现还有两处等价调整：伴随矩阵直接读取 `f.coeff i * f.leadingCoeff⁻¹`，因此不先生成
首一化后的整张系数表；子式的 OR 和两个判据的 AND 采用依次求值的平衡树，不依赖短路。
这些调整的正确性和空间界均已证明；原文首一化和零导数分支的数学说明也有独立定理。

## 资源证明

取原始输入位数为 `L`。具体编码给出：

- 主多项式次数的位数至多 `L`。
- 有限域大小 `q` 的位数至多 `L²+1`。
- Frobenius 指数 `q*j` 的位数至多 `L²+L+1`。
- 每个实际域标量的编码长度至多 `2L²+2L`。
- 每阶段初始地址的 rank 至多 `100(L+3)⁴`；所有执行前缀的栈深都满足同一界。
- 三阶段局部转移次数至多 `2^(100(L+3)⁴+6)`，该巨大工作量是证明中的上界，不是运行时
  保存的一张表或一个一元计数器。

有限求和和子式检查使用平衡地址递归；不同分支依次执行，返回后复用空间。
保守的多项式界足够导出 `PSPACE`，没有把递归深度本身直接当作工作带空间。
实际编码长度还单独计入每个地址字段、每个返回标量、帧标记和控制状态。

三阶段配置码各自至多 `10⁶(L+3)⁸` 位；加上原始输入副本及阶段标签后，完整控制状态码
至多 `2·10⁶(L+3)⁸` 位。运行状态以 `00` 开头，初始化输入以 `01` 开头，完成状态为
`[true, answer]`，避免不同用途的字符串发生冲突。低层 TM 的最终空间多项式还包含
`G ∈ FP` 所提供的单步实现工作区，由 `streamingMachine_exists` 的空间复合定理给出；
上述 `2·10⁶(L+3)⁸` 是控制状态编码界，不冒充整个低层 TM 的精确空间界。

引理 17 的通用 oracle 版本不要求条目查询属于 `FP`。它保存行列式续延栈，逐步运行
给定的条目 oracle，返回后复用其工作区。只以前提记录原条目 oracle 的正确性、终止和
每次查询每个前缀的 `S` 位空间界，证明整个协程返回真实行列式，并满足
`2*(2*w+(2*w+7)*berkowitzStackBound n+4)+S+3` 的编码长度界。
这里 `w` 界定地址和域标量的位长；没有假设完整行列式算法的空间界。
`lemma17_faithful_space_composition` 进一步要求三种输入编码单射，证明协程整体编码单射，
排除把不同配置编码为同一短字符串所造成的虚假空间解释。

## 边界和覆盖

零多项式、常数、一次多项式、零导数、非零常数导数、重因子和所有有限特征均已纳入。
空行列式等于 `1`，因此一次多项式所需的零阶子式也正确处理。
模多项式不可约性不是输入前提：先在已验证的 `ZMod p` 上运行同一多项式判定，随后才
建立扩张域的 `Field` 实例。

公式 (47) 通过 `t=z⁻¹` 对应的形式幂级数证明；不需要把 Laurent 级数或行列式公式作为
额外前提。公式 (49) 的一般因子个数等式也已证明，范围不限于“不可约时维数为 1”。

## 验证记录

本次新增 `Section4/` 下 49 个 Lean 模块，并通过 `Section4Complete.lean` 纳入项目总入口。

| 检查 | 结果 |
|---|---|
| `lake build` | 通过，9399 项构建任务。 |
| `lake env lean scripts/Axioms.lean` | 419 项声明全部通过；输出见 `docs/AXIOMS.txt`。 |
| `lake env lean scripts/DepAudit.lean` | 403 个入口，传递闭包含 83,534 个常量；仅到达 `propext`、`Quot.sound`、`Classical.choice`。 |
| 新增代码未证明项／不受内核验证机制扫描 | 没有 `sorry`、`admit`、自定义 `axiom`、`native_decide`、`implemented_by`、`extern` 或 `unsafe`。 |
| `scripts/check_vendor.sh` | 全部 38 个 vendored 模块与固定来源提交完全相同。 |
| `git diff --check` | 通过。 |

审计认证上述定理及证明项；它不会自动证明参数 `UniformLocalStepRealization G` 有具体实例。
该低层单步实现仍按范围约定明确保留。
