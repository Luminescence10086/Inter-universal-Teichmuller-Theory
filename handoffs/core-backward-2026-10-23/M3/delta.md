# M3 delta: what the existing interfaces retain, and what K1/K4 still need

静态阅读，无 Lean/lake/构建。T2 的八张卡片按引用复用（`handoffs/core-support-2026-10-22/T2/cards.json`，
sha256 `25a28fd7…`）；本页只谈 M3 新增的 11 项，不重述卡片。四个仓库 HEAD 与计划一致，无 `INPUT_DRIFT`。

## 1. 这 11 项实际保留了什么

**（a）一个不具执行内容的输出函数。** `EtaAlg.out`（EtaAlg.lean:108-109）是一个结构字段：对任意
`B : BPS model D.bpsDegrees.bad`、任意 Hodge theater `h`、任意 Step-1 同构 `ι`、任意 `S : Ind3 D` 给出一个
`Region D`。字段本身不含算法、轨迹或可执行性；docstring 说的是 η-算法，字段说的是一个函数。这是 **K4 缺口的
最锐点**：11 项里 `legal_execution_path` 全部为 false。

**（b）三条对 `out` 的约束，而不是对它的构造。** `ind12_acts_on_S`（112-114）是"存在 τ 使两次取值相等"；
`etUnitOnly`（117-119）是"存在 f 使 `out ι S = f ι.et S`"；`realisation`（123-125）是"每次取值都满足
`IsAdelic ∧ InHullOfImage`"。三者都是关于既有 `out` 的性质，没有一条要求 `out` 由某程序产生。

**（c）选择集独立于算法。** `Ind3`（Ind3.lean:213）只由 `IsAdelic` 与 `S i ≤ hullOf D (vcI D) i` 切出；
Ind3.lean 只 import `Iut.Wall.Rss`，全文不出现 `EtaAlg`、`out` 或 q-pilot。所以"允许的 S"先于任何算法而定，
算法与选择集只在 EtaAlg 的字段类型里相遇。

**（d）q 几乎不在场。** 11 项中只有两项在自身语句里点名 q 量：`LGPLattice.kum_gen`（Thm311LGP.lean:97-98，
经 `gaussGen` = `EtaleTheta.lgpValue`，其 docstring 称 `q_v^{j²}`）与 `EtaAlg.ThetaShift`
（MultiContainer.lean:107，`D.qPilot.absLogQ`）。`Choice`（141）指向的是 **Θ**-pilot BPS（`D.thetaValD`），
不是 q-pilot；q 只在 `Wall`（173-175）与 `etaAnab_eq_etaQ_iff`（151-152）里通过把 `B` 实例化为 `A.qBPS` 才进来。
`out`、`ind12_acts_on_S`、`etUnitOnly`、`realisation`、`IsAdelic`、`InHullOfImage`、`Ind3` 的语句里没有任何 q 项。

**（e）Kummer 数据被限定为 unit-induced。** `LatticeKummer`（Kummer.lean:248-252）两个字段：`kum : ℤ×ℤ → Scaling D`
与 `unit : ∀ a, UnitInducedScaling D (kum a)`。同文件 `shift_eq_zero_of_unitInduced`（203-205）说明 unit-induced
的 log-volume 移位为 0，而 `not_unitInducedScaling_qScale_zpow`（238-240）说明 `qScale^m (m≠0)` 不是 unit-induced。
两条合起来的直接后果：该结构的 Kummer 数据不能提供 q-移位。

## 2. 对 K1 的落差（带来源的执行记录）

- **没有联合记录。** 没有任何一个声明把 `(D, A, B, h, ι, S)` 收进一个带类型的对象；它们只在各条语句里以
  独立参数出现。`out` 是字段，`A` 是参数，二者之间没有"这是同一个输入"的凭证。K1 要的忠实类型，在这 11 项里
  没有对应物。
- **Choice 与 q 分离。** Step-1 选择被定义为到 Θ-pilot 的同构（141 + 138），因此"选择"这一环节本身不含 q 数据；
  q 的出现完全靠在**使用处**把 `B` 取成 `A.qBPS`。若 K1 要把 q 侧选择与 Θ 侧选择记成同一份记录，本接口不给。
- **`Side` 与格点顶点无关联。** `EtaAlg.Side`（100）是不透明类型；`LogThetaLattice.H : ℤ×ℤ → ThetaPmEllNFHT D`
  （Lattice.lean:92）是另一个不透明族，两者之间没有任何声明把它们识别起来。这是 M3 只记录、不解释的一点。
- **`LatticeKummer` 的参数 `L` 是空参数。** 两个字段的类型里都不出现 `L`；docstring（246-247）说"每个顶点
  `(n,m)` 的容器"，但字段只按 `ℤ×ℤ` 索引、取值在 `Scaling D` 里，不含任何指向 `L.H (n,m)` 的项。此处只记录
  源码事实，不断言意图。

## 3. 对 K4 的落差（原始允许输出实现）

- **`realisation` 是条件，不是实现。** 它说每个输出是 adelic 且落在**某一个** (Ind1)-image 的 holomorphic hull
  里；它**没有**说每个 adelic 或 hull 内的区域都是输出，也没有任何反向满射的断言。`InHullOfImage`
  （Rss.lean:338-339）是单向包含 `U i ≤ hullOf D (thetaImage D l) i`，而 `InImage.inHullOfImage`（350）说明 hull
  要求比 image 要求更弱（T2 卡片 1 已记此点）。
- **degree 比较不在接口里。** 11 项中唯一带 degree 等式的是 `ThetaShift`（107），而且它是**等式**，不是不等式；
  真正的上界是独立定理：`logVol_le_rhs`（Rss.lean:374-375）、`logVol_le_vcI`（Ind3.lean:244-245）、
  `SSIneq`（MultiContainer.lean:88-89）。接口层没有一处要求比较。
- **`ThetaShift` 是对任意 `A` 的 Prop，不属结构。** 因此一个模型可以满足它而 `out` 仍非实现；它的inhabitant
  由别处构造（`theaterAlg_thetaShift`，HodgeTheater/Wall.lean:108；`model_thetaShift`，Thm311.lean:185）。
- **`Ind3` 的 log-volume 满射说的是输入。** `exists_ind3_logVol_iff`（Ind3.lean:253-254）证明 `Ind3` 上 log-volume
  的值域是整个半线 `x ≤ log-vol(hull(VC(I)))`。这是关于**选择集 S** 的定理，`out` 不出现在 Ind3.lean 里，
  不能转写成"输出覆盖"。

## 4. localization：位置索引到处有，localization 映射一处也没有

11 项都含位置/素数索引数据（`Region` 是 capsule 族，Rss:314；`EtUnitIso` 逐 v，BPS:147；`Scaling.u` 逐
capsule×prime×tuple，Scaling:121-126；`arc`/`kum_gen` 逐 infinite/finite place，Thm311LGP:95,97-98），但这些
签名里**没有出现** local→global 的映射、局部数据与全局对象的识别、或局部之间的相容图。`IsAdelic`（Rss:319-320）
只要求每个分量各自 admissible，分量之间不要求任何关系。这是 K2 侧的直接落差，M3 只按签名记录。

## 5. 复用与边界

- T2 卡片 1（`Iut.Wall.EtaAlg` 整体，96-125 与八字段表）、卡片 2/3（同文件定理）、卡片 4-8（另三个仓库）不被
  本任务重做；M3-01/03/04/05 是卡片 1 的字段级补充，未与卡片 1 冲突。
- `restriction_kummer_thetaUnit` 属 `tate-curves-theta` 的 `TateCurvesTheta.TateParameter`（T2 卡片 7 已更正），
  M3 未依赖它。
- 作用域补前提的情况：`LatticeKummer` 的 `variable {D}`（Kummer.lean:244）把 D 变隐式；`LGPLattice` 的
  `variable (D) in`（Thm311LGP.lean:89）把文件级隐式 D 变显式；`IsAdelic`/`InHullOfImage`/`Ind3` 在 `universe u`
  下对 `InitialThetaData.{u}` 声明（Rss:55,300；Ind3:51,55），而 EtaAlg 全程 `.{0}`。三者都是作用域读法，
  **未运行 elaborator**。
- 两处禁止项已按计划避开：(a) 只记"源码未在该字段中要求 X"，未推"原 IUT 缺 X"；(b) 条件字段与 hull 落点
  未报成反向满射。
