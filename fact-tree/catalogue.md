# 已验收定理总入口

共 135 个节点、115 条边；来自三个工程、两个工具链。

目录是调用入口，不是跨工具链的 Lean import。没有证明真实 IUT 或 abc。

| 工程 | 节点 | 边 | Lean | 逐项目录 |
|---|---:|---:|---|---|
| core | 38 | 14 | Lean (version 4.34.0, x86_64-w64-windows-gnu, commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b, Release) | [声明与依赖](index.md) |
| local-field | 24 | 31 | Lean (version 4.34.0-rc2, x86_64-w64-windows-gnu, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d, Release) | [声明与依赖](../local-field/fact-tree/index.md) |
| bridge | 73 | 67 | Lean (version 4.34.0-rc2, x86_64-w64-windows-gnu, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d, Release) | [声明与依赖](../bridge/fact-tree/index.md) |

查询：`python tools/forest.py query 关键词`；深查：追加 `--deep`。
重建本入口：`python tools/forest.py refresh --deep`。

实际准入依据仍为各工程 facts.json。查询会重新检查源快照，深查会重算运行产物哈希。
其中 3 条跨工程边来自 local-field → bridge 的实际 import；接口合同不混入证明边。
registry.json 和 combined.dot 是可重建快照；源代码变化后须重新验证并 refresh。
