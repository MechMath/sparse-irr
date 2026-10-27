# 形式化范围约定

用户于 2026-10-22 明确约定，后续会话应继续遵守：

- 论文引用的外部定理均可作为显式 Lean 前提，无须在本项目重新证明。
- 本文内部的数学定理及推导过程必须由 Lean 证明，不能列为外部前提。
- 论文中的算法步骤、低层机器实现及其实现验证可以不形式化。
- 最终结论仍须有 Lean 定理，不能因省略算法而把最终结论排除范围。

使用定理参数或命名的 `Prop` 接口记录外部输入，不添加全局自定义公理或 `sorry`。
区分文献定理前提与省略算法所留下的实现接口；最终定理的声明和文档须列明两者。
不能把实现接口称为已证明的外部定理，也不能直接假设本文要证明的最终结论。

第 3 节当前范围和主要入口见 [docs/PRIME_COUNTING_QRH.md](docs/PRIME_COUNTING_QRH.md)。

第 4 节当前范围、最终定理及低层局部实现接口见
[docs/SECTION4_FORMALIZATION_2026-10-22.md](docs/SECTION4_FORMALIZATION_2026-10-22.md)。
用户于 2026-10-23 进一步要求第 4 节的算法、低层二进制实现、通用 oracle 协程编译及
完整机器认证均补齐，不再省略这部分实现。原 `UniformLocalStepRealization` 已由实际
`section4BinaryStep` 的证明构造；当前无实现参数的最终入口是
`section4_irreducibility_mem_PSPACE_unconditional` 和 `section4_complete_machine`。
最新机器认证情况见
[docs/SECTION4_MACHINE_CERTIFICATION_2026-10-23.md](docs/SECTION4_MACHINE_CERTIFICATION_2026-10-23.md)。
