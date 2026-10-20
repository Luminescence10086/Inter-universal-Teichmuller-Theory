# 第五轮：第四轮基线重复性审计

**结果：PASS。** 在第五轮新源码创建前，两套工程的 `query.py --deep` 均以退出码 0 完成；汇总仍为 57 个准入节点、35 条边。

| 工程 | 深度查询 | 节点/边 | 收据目标 | Lean 诊断（收据记录） |
|---|---:|---:|---:|---|
| 主工程 | 通过 | 38 / 14 | 38 | 5 个证明源文件均已检查，0 error、0 warning；当前文件哈希与收据一致 |
| local-field | 通过 | 19 / 21 | 19 | Filtration、Shell 均已检查，0 error、0 warning；当前文件哈希与收据一致 |

两个 fact-tree 的传递公理集合均为 `propext`、`Classical.choice`、`Quot.sound`，均在白名单内。两个收据的输入快照及观察文本哈希绑定匹配。主工程采用第四轮保留的第三轮 VS Code 观察（76 条 information）；local-field 使用第四轮 VS Code 观察（38 条 information）。这些是既存 UI 观察；本轮深度查询仅作为 CLI 结果记录，没有被视为新的 VS Code 观察。

`GAP.md` 的 G01–G06 六项仍标记 open；`research/round3-realization-obligations.md` 的 RI-01–RI-08 八项状态均为 open。本机 Mathlib HEAD 为 `85e3a25e006c35636f0e53b0e9296caca2685bc0`。完整机器核对及收据路径见 [round5-baseline-audit.json](../verification/round5-baseline-audit.json)。

此审计没有运行完整 `verify.py`，也没有修改 Lean、tools、配置、fact-tree、receipt 或外部 Mathlib。

