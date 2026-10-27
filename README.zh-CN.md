# 稀疏整数多项式不可约性的 Lean 4 形式化

[English README](README.md) · [论文对应表](docs/PAPER_1021_MAP.md)

本仓库提供论文

> **Irreducibility Testing of Sparse Polynomials over Integers is NP-hard and Probabilistic Polynomial Time**

的**第2、3节整数不可约性结果**的 Lean 4 形式化：无条件硬度证明，以及明确文献前提下的
`PP`／`PSPACE` 上界，包含内部数学推导和整数算法机器。

## 主要结果

- 整数不可约性的 many-one coNP-hardness、可约性的 many-one NP-hardness，以及不可约性的一次查询 Turing NP-hardness。
- 整数不可约性属于 `PP` 和 `PSPACE`：保留有效素理想计数估计和 AKS 判素定理为显式参数。
- 判别式、异常素数、模根与素理想对应、平均估计、实数截断、阈值判据及备注16的任意固定正间隙推广。
- 实际严格多数机器、全路径多项式时限和精确接受概率；确定性枚举及空间证明。

```lean
import SparseIrred

#check SparseIrred.Irreducibility.irreducibility_hardness
#check SparseIrred.UpperBounds.section3_irreducibility_mem_PP_and_PSPACE_of_external_theorems
```

§3.6 的不依赖 AKS 的线性空间定理从指定的已预处理核心配置开始；全原始输入的直接
`PSPACE` 路线使用 AKS。`PP` 是严格多数接受，不表示 `BPP` 的固定成功率间隙。

## 构建与审计

安装 elan、Git、Bash、Python 3 和 ripgrep。工具链是 **Lean `v4.34.0-rc2`**，
依赖版本固定在 `lake-manifest.json`；复现时不要运行 `lake update`。

```sh
git clone https://github.com/MechMath/sparse-irr.git
cd sparse-irr
lake exe cache get
lake build
scripts/audit.sh
scripts/check_vendor.sh
```

无需本机兄弟仓库或论文 PDF。38个 vendored 模块附有与原提交核对的 SHA-256 清单。
审计脚本在构建失败、未证明项、未知公理或校验失败时退出失败。
当前范围的检查结果见 [发布记录](docs/RELEASE_2026-10-27.md)。

## 外部前提

目标稿 §3.1 的 **[6] Cureton–Thorner** 提供零点自由输入，**[9]
Frei–Sofos–Widmer，定理1.1** 提供有效计数；本项目通过 `EffectivePrimeIdealEstimate`
等命名接口接收计数结论，未导入参考文献 **[2]** 的外部 Lean 项目。
§3.7 的 **[1] Agrawal–Kayal–Saxena，“PRIMES is in P”** 对应 `BinaryPrimalityInFP`。
本文自己的平均估计和最终结论是内部证明，不作为外部假设。

代码无自定义全局公理和 `sorry`。公理审计只到达 `propext`、`Classical.choice`、
`Quot.sound`，但不自动证明显式的文献参数。例1、历史介绍和开放问题不单独计入形式化声明。

## 说明文件

- [论文编号与 Lean 对应](docs/PAPER_1021_MAP.md)
- [第3节完成报告](docs/SECTION3_COMPLETION_2026-10-22.md)
- [第3节详细 term 表](docs/SECTION3_LEAN_MAP.md)
- [第3节机器实现报告](docs/SECTION3_MACHINE_IMPLEMENTATION_2026-10-22.md)
- [依赖与前提](docs/DEPENDENCIES.md)

## 许可证

本仓库采用 **Apache License 2.0**，完整条款见 [LICENSE](LICENSE)。
单独获取的依赖保留各自许可证；vendored 文件来源见 [Vendor 说明](Vendor/README.md)。
