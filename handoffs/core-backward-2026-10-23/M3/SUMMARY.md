# M3 SUMMARY

- 状态 `STATIC_ONLY`；四个固定仓库 HEAD 与计划一致，`git status` 干净，无 `INPUT_DRIFT`；未运行 Lean/lake/构建/编辑器。
- 11 项全部在 `external/iut`：`EtaAlg.out`(EtaAlg.lean:108-109)、`Choice`(141)、`ind12_acts_on_S`(112-114)、`etUnitOnly`(117-119)、`realisation`(123-125)、`IsAdelic`(Rss.lean:319-320)、`InHullOfImage`(Rss.lean:338-339)、`Ind3`(Ind3.lean:213)、`LatticeKummer`(Kummer.lean:248-252)、`LGPLattice`(Thm311LGP.lean:93-98)、`ThetaShift`(MultiContainer.lean:105-107)。
- 名称修正：`ThetaShift` 全名是 `Iut.Wall.EtaAlg.ThetaShift`（名字扩展），不是 `MultiContainer.ThetaShift`。
- 作用域确实加前提的：`Choice`/卡片的 `EtaAlg` 字段随 `variable (D)`（EtaAlg:92, 129）；`LatticeKummer` 的 `variable {D}`（Kummer:244）把 D 变隐式；`LGPLattice` 的 `variable (D) in`（Thm311LGP:89）把隐式 D 变显式；`IsAdelic`/`InHullOfImage`/`Ind3` 在 `universe u` 下对 `InitialThetaData.{u}` 声明。
- 四个 flag：**合法执行路径 false × 11**；**native q 标记仅 2 项 true**（`LGPLattice` 经 `gaussGen`=q_v^{j²}；`ThetaShift` 经 `D.qPilot.absLogQ`）；**localization 数据 11 项 true，但全是位置索引/分量条件，无一处要求 localization 映射**；**degree 比较仅 1 项 true 且是等式**（`ThetaShift`），所有不等式都是别的定理（`logVol_le_rhs` Rss:374、`logVol_le_vcI` Ind3:244、`SSIneq` MultiContainer:88）。
- 值得注意的"源码未要求"三处：`out` 未要求任何执行/算法（字段）；`realisation` 未要求 degree 上界（上界是定理）；`LatticeKummer.unit` 因 unit-induced 且 `qScale^m` 非 unit-induced（238-240），Kummer 数据不能提供 q-移位。
- 两处禁止项已避开：未由"源码未要求 X"推"原 IUT 缺 X"；未把条件字段或 hull 落点报成反向满射（`Ind3` 的 log-volume 满射是关于输入 S 的，`out` 不在该文件）。
- 复用：T2 八卡按引用复用，M3-01/03/04/05 仅为其卡片 1 的字段级补充；未重做卡片 2-8。
- `LatticeKummer` 的参数 `L` 在字段类型中不出现（空参数）；`EtaAlg.Side` 与 `LogThetaLattice.H` 无声明关联——两点只记录，解释进 `QUESTIONS.md`。
- 9 项解释性歧义（q-power 是否算 q 标记、等式是否算 degree 比较等）已进 `QUESTIONS.md`。
- 交付：`interfaces.json`、`delta.md`、`QUESTIONS.md`、`SUMMARY.md`、`delivery.json`；`lean_run=false`、`editor_run=false`、`fact_tree_admitted=false`。
