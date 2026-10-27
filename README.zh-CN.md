# 稀疏多项式不可约性的 Lean 4 形式化

[English README](README.md) · [非独立稿全篇对应表](docs/PAPER_1021_MAP.md)

本项目对应 **18 页非独立稿 `1021-AI4Math_Irreducibility.pdf`**，包括整数不可约性的
复杂性下界、第3节整数上界，以及第4节有限域上的均匀多项式空间算法和完整机器认证。

目标稿的全部编号定理、引理、命题、推论及备注16都有 Lean 对应。这里不声称每一句
叙述都独立形式化：引言例1的完整因式分解输出长度讨论没有专门声明；历史介绍、开放问题
及被引用文献的全部结果也不属于本项目重证范围。旧笔记和7页版本编号不同，统一以
[18页稿对应表](docs/PAPER_1021_MAP.md) 为准。

## 主要结论

- 整数不可约性的 many-one coNP-hardness、可约性的 many-one NP-hardness，以及
  不可约性的一次查询 Turing NP-hardness：无条件证明。
- 整数不可约性属于 `PP` 和 `PSPACE`：以明确的外部有效素理想计数估计与 AKS 判素定理
  为参数。论文内部的判别式、异常素数、模根对应、平均估计、阈值判据及机器组合均有证明。
- 有限域不可约性属于 `PSPACE`：**没有数学或实现参数**。已实现并认证二进制程序、
  有限域运算、全部输入验证、Berkowitz/Frobenius 计算、实际确定性机器及所有运行前缀的空间界。
- 引理17：给定满足正确性、终止和空间契约的真实条目机，构造完整输出行列式编码的统一
  图灵机。条目机采用包含输出头界的 `WithinDecisionSpace` 模型。

完整导入：

```lean
import SparseIrred
```

主要入口：

| 结论 | Lean term |
|---|---|
| 定理2、4的硬度 | `SparseIrred.Irreducibility.irreducibility_hardness` |
| 定理2、10的整数上界 | `SparseIrred.UpperBounds.section3_irreducibility_mem_PP_and_PSPACE_of_external_theorems` |
| 定理3、18的有限域上界 | `SparseIrred.UpperBounds.Section4.section4_irreducibility_mem_PSPACE_unconditional` |
| 第4节完整机器认证 | `SparseIrred.UpperBounds.Section4.section4_complete_machine` |
| 引理17的通用行列式机器 | `SparseIrred.UpperBounds.Section4.lemma17_uniform_scalar_machine` |

## 构建与审计

安装 elan、Git；审计脚本还需要 Bash、Python 3 和 ripgrep。Lean 工具链及依赖版本全部
固定在 `lean-toolchain`、`lakefile.toml` 和 `lake-manifest.json`，复现时不要运行 `lake update`。

```sh
git clone https://github.com/MechMath/sparse-irr.git
cd sparse-irr
lake exe cache get
lake build
scripts/audit.sh
lake env lean scripts/Section4Smoke.lean
```

工具链是 **Lean `v4.34.0-rc2`**；无需本机兄弟仓库、论文 PDF 或会话记录。
`scripts/check_vendor.sh` 使用随库发布的 SHA-256 清单检查全部38个 vendored 模块。
审计脚本遇到构建错误、未证明项、额外公理或 Vendor 不一致会退出失败。

公理审计只到达 Lean 的 `propext`、`Classical.choice` 和 `Quot.sound`；项目没有自定义
全局公理或 `sorry`。**这不意味着已证明定理参数中的外部文献估计。** 最新验证记录见
[发布检查记录](docs/RELEASE_2026-10-27.md)。

## 外部前提与机器范围

第3节最终保留的外部前提对应目标稿：

1. §3.1 **[6] Cureton–Thorner** 的 Dedekind zeta 零点自由输入，以及 **[9]
   Frei–Sofos–Widmer，定理1.1** 的有效计数结果。本项目以 `EffectivePrimeIdealEstimate`
   等命名接口接收计数结论，没有导入参考文献 **[2]** 的外部 Lean 仓库，也没有假定本文
   自己要推导的平均估计。
2. §3.7 **[1] Agrawal–Kayal–Saxena，“PRIMES is in P”**，接口为 `BinaryPrimalityInFP`。

§3.6 的不依赖 AKS 的线性空间结果从明确的已预处理核心配置开始；全原始输入的直接
`PSPACE` 路线仍使用 AKS。这里的 `PP` 是严格多数接受，不等同于 `BPP`。

第4节旧的 `UniformLocalStepRealization` 已由实际 `section4BinaryStep` 构造，最终定理
不再要求提供这一实现接口。引理17的条目机条件是引理的输入假设，不是遗漏的协程实现；
其配置模型明确包含输出头窗口。

## 进一步阅读

- [全篇编号、公式与 Lean 对应](docs/PAPER_1021_MAP.md)
- [第3节完成报告](docs/SECTION3_COMPLETION_2026-10-22.md)
- [第3节详细 term 对照](docs/SECTION3_LEAN_MAP.md)
- [第4节数学推导](docs/SECTION4_FORMALIZATION_2026-10-22.md)
- [第4节完整机器认证](docs/SECTION4_MACHINE_CERTIFICATION_2026-10-23.md)

本源码快照尚未指定项目统一许可证；本说明不自行添加授权条款。依赖项目保留各自许可证，
vendored 文件来源见 [Vendor 说明](Vendor/README.md)。
