# 论文第3节：整数不可约性上界

论文：**Irreducibility Testing of Sparse Polynomials over Integers is NP-hard and Probabilistic Polynomial Time**。

当前发布保留整数不可约性的 `PP` 和 `PSPACE` 上界、内部数论推导与已验证机器。
本文献前提以定理参数记录，不添加全局公理，不把本文自己的结论作为假设。

## 主要入口

- `SparseIrred.UpperBounds.Section3Complete`：统一导入入口。
- `section3_irreducibility_mem_PP_and_PSPACE_of_external_theorems`：实际整数语言的最终结论。
- `GeneralGap.section3_irreducibility_mem_PP_and_PSPACE_of_positive_gap`：备注16的固定正间隙。
- `integer_prime_root_average_concrete_real`：命题13的任意实数截断。
- `Machine.section3_deterministic_streaming_mem_PSPACE`：全输入确定性枚举。
- `Machine.section3_linear_streaming_core`：预处理后 trial-division 核心的线性空间。

最终上界的文献输入为有效素理想计数估计和 AKS 二进制判素属于 `FP`；内部平均估计、
截断、不可约阈值、见证计数和实际机器概率均有证明。具体引用对应目标稿[6]、[9]和[1]。
公理检查认证条件式证明项，不自动证明这些外部输入。

详细说明见 [第3节完成报告](SECTION3_COMPLETION_2026-10-22.md)、
[Lean 对应表](SECTION3_LEAN_MAP.md)、[当前范围](PRIME_COUNTING_QRH.md) 及
[发布检查](RELEASE_2026-10-27.md)。
