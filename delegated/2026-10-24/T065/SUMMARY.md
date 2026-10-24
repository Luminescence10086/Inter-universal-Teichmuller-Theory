# T065 · 逐字段来源追溯：`StripKummer` 等处，哪些字段由定义生成、哪些由 structure 字段提供

状态：`RESEARCH_ONLY` · base_commit `8d60456043e30a3da79cc838d03a19b80675dc98` · 未编译任何 Lean。

## 结论（一句话）

四个 Kummer 环境（`StripKummer`/`GalKummer`/`AnabelianKummer`/`LatticeKummer`）共 **11 个字段，
全部由 structure 字段提供（DEF=0）**；把表 A 的 8 个环境一起算，**22 个字段，定义生成 0**。
仓库里**唯一**的"定义生成"落在把环境沿导出链重写的那些定义上（表 B，10 个），而它们生成的是
*下游*字段（且 `kum` 一路拷贝），不是上游环境自己的字段。任务要求交的双向表见下。

## 表 A · 每个环境：定义生成 / structure 提供（字段级，逐个点名）

| # | 环境 | 声明位置（文件:行，SHA256 已复核） | 定义生成 | structure 提供 | 判据 |
|---|---|---|---|---|---|
| 1 | `RigidDGalStrip` | `Iut/HodgeTheater/StripLift.lean:428` | **0** | **2** | `strip`(:430)、`kappa`(:432) 无任何声明以其类型为结果类型；`taut`(:438) 是退化值（`tautological` + `refl`） |
| 2 | `LatticeKummer` | `Iut/LogLink/Kummer.lean:248` | **0** | **2** | `kum`(:250)、`unit`(:252)；只被 `trivial`(:294)/`alt`(:300) 填过，`alt` 的 `kum` 直接取自 `LatticeKummer.alt.kum` |
| 3 | `AnabelianKummer` | `Iut/LogLink/GalKummer.lean:361` | **0** | **2** | `kum`(:363)、`anab`(:365)；只被 `alt`(:396) 填过，`alt.kum := (LatticeKummer.alt L).kum` |
| 4 | `GalKummer` | `Iut/LogLink/GalKummer.lean:368` | **0** | **2** | `kum`(:370)、`gal`(:372)；只被 `trivial`(:428) 填过（`kum ≡ 1` 退化） |
| 5 | `StripKummer` | `Iut/LogLink/StripKummer.lean:168` | **0** | **5** | `strip`(:170)、`coric`(:172)、`link`(:174)、`kum`(:176)、`scale`(:178)；`trivial`(:218) 全退化（`taut`/`refl`/`1`） |
| 6 | `BiCoricKummer` | `Iut/LogLink/Thm311Rest.lean:164` | **0** | **4** | `cor`/`kum`/`env`/`envIso`；`ofLattice`(:181) 的 `kum` 取 `(PrimeStrip.nonempty_iso _ _).some`——任意选取，非构造 |
| 7 | `FullKummer` | `Iut/LogLink/GalKummerAll.lean:535` | **0** | **2** | `non`(:537)、`arc`(:539) |
| 8 | `FullGalKummer` | `Iut/LogLink/GalKummerAll.lean:544` | **0** | **3** | `non`(:546)、`arc`(:548)、`gal`(:550) |

合计 **8 个环境 / 22 个字段：定义生成 0，structure 提供 22。**

## 表 B · 反向（定义生成的，全部是下游字段或残差）

| 声明 | 位置 | 实际生成的字段 | 性质 |
|---|---|---|---|
| `StripKummer.gal` | `StripKummer.lean:185` | 一个新的 Galois 自同构族 | **真构造**：`= RigidDGalStrip.gal (K.link a) w`（:186）。但输入仍全是 `StripKummer` 的 `link` 字段 |
| `StripKummer.toGalKummer` | `:189` | `GalKummer.gal` | 由 `(K.scale a).galInduced` 生成；**`kum` 是拷贝** `K.kum` |
| `StripKummer.toLatticeKummer` | `:192` | `LatticeKummer.unit` | 经 `toGalKummer` 逐层放电；`kum` 一路拷贝 |
| `StripKummer.liftIso` | `:206` | Frobenioid 侧提升 | `= RigidDGalStrip.liftIso (K.link a)`，读 `link` |
| `GalKummer.toAnabelianKummer` | `GalKummer.lean:412` | `AnabelianKummer.anab` | 由 `(K.gal a).anabelian` 生成；`kum` 拷贝 |
| `GalKummer.toLatticeKummer` | `:415` | `LatticeKummer.unit` | 两层转接，`kum` 拷贝 |
| `AnabelianKummer.toLatticeKummer` | `:379` | `LatticeKummer.unit` | 由 `(K.anab a).unitInduced` 生成；`kum` 拷贝 |
| `FullKummer.kum` / `.toLatticeKummer` | `GalKummerAll.lean:557/560` | `FullScaling`、`unit` | 组装 `(K.non.kum a, K.arc a)`，不新造标尺 |
| `FullGalKummer.toFullKummer` | `:635` | `FullKummer.non` | `K.non.toAnabelianKummer` + `K.arc` |

共 **10 个 DEF_GEN 定义**（`trace_fields.py` 只登记了 7 个，遗漏 `FullKummer.kum`、
`FullKummer.toLatticeKummer`、`FullGalKummer.toFullKummer`；`StripScaling.galInduced`/`shift_eq_zero`
两个是 `Prop` 证明项、不产出字段，故不计入）。**十个的目标字段全在别的 structure 上，无一产出上游环境字段。**

**要义**：这些定义的输出类型都是*别的* structure。整个仓库里**没有任何声明**以 `ℤ×ℤ → Scaling D`、
`ℤ×ℤ → RigidDGalStrip D`、`DGalStrip D` 或 `ArcScaling D` 的**构造者**身份出现——`Scaling` 自己的
`u` 字段（`Iut/Wall/Scaling.lean:121,123`）在定义处就是任意的。

须分清**类型**与**值**：`DGalStrip`（`StripLift.lean:373`）和 `ArcScaling`（`GalKummerAll.lean:408`）本身
确是 `abbrev`，即"类型由定义给出"；但它们的**取值**仍是环境字段，且唯一的填充者是退化项
（`PrimeStrip.tautological : PrimeStrip K M` / 常量 `1`）。**类型由定义生成 ≠ 字段由定义生成。**

## 表 C · 标尺本身从哪里来（唯一的"半构造"）

`factor` 层标尺 `b` 只有一处是**真算出来的**，且带前提：

- `exists_factorGalInduced_of_linear`（`GalKummer.lean:215`）：给定 `hov : IsOver K p v` 与
  **线性性** `hlin`（诱导的 ψ 是 `K_v`-线性的），才产出 `b := Units.mk0 (ψ 1)`。前提是输入，不是结论。
- 其余全是退化：`factorGalInduced_one`(:231)、`factorUnitsAut_neg_one`(:238)、
  `factorUnitInduced_one`(`Kummer.lean:158`)、`factorUnitInduced_neg_one`(:162)——只有 `b = 1` 与 `b = -1`。

## 未解决（`UNRESOLVED`）

1. **`StripKummer.strip`** — 未找到任何以 `ℤ×ℤ → RigidDGalStrip D` 为结果类型的声明。`LogThetaLattice.H`
   端点是 `ThetaPmEllNFHT D`（剧场，不是 strip），**字段名相近不算实现来源**，故记 `UNRESOLVED`。
2. **`StripKummer.coric`** — 只有 `RigidDGalStrip.taut`（退化）可产出；任何列/顶点的 coric strip 均未构造。`UNRESOLVED`。
3. **`StripKummer.link`** — `PrimeStrip.nonempty_iso`(`PrimeStrip.lean:227`) 说明任意两条 strip 都同构，
   故该字段**可证可填但内容是任意的**，不携带来源信息。`UNRESOLVED`（可填 ≠ 有来源）。
4. **各环境的 `kum`** — 4 处同名字段，彼此靠拷贝相连，源头仍是任取的 `Scaling`。`UNRESOLVED`。
5. **`FullKummer.arc` / `FullGalKummer.arc`** — `ArcScaling` 是 `abbrev`（`GalKummerAll.lean:408`），
   无构造声明；只在 `trivial`(:618/:653) 里填 `1`。`UNRESOLVED`。

## 复现

```
python delegated/2026-10-24/T065/replay.py --root . --out delegated/2026-10-24/T065/logs
python delegated/2026-10-24/T065/preflight.py --run
```

两次 replay stdout **逐字节相同**（SHA256 `940c7f86…3d5e92`）；`fields.json` 与 `pins.json` 两次同哈希。

## 官方预检

命令（在仓库根执行）：

```
python handoffs/agent-batch-2026-10-24/check_delivery.py \
    --delivery delegated/2026-10-24/T065/delivery.json
```

实际输出（exit code **0**，`logs/preflight.stdout.log`，SHA256
`4e73ff6ea4a3eb4112b2e0d4fc017074319c9b41f86c450359d6fbe7e2aa02be`，236 字节）：

```json
{"result": "PACKAGE_COMPLETE", "task_id": "T065", "reported_status": "RESEARCH_ONLY", "scope": "Material and hashes only. No reported command executed; mathematics, axioms, source semantics and editor observations remain unverified."}
```

**预检通过的边界**（照 PROTOCOL.md 第 28 行）：只查材料与哈希，**不执行**交付代码，**不判**数学语义。
`PACKAGE_COMPLETE` 不等于 Lean 通过、更不等于核心 gap 通过。本任务不编译 Lean，故无公理日志。

### 预检的一个自指陷阱（已解，留记）

`check_delivery.py` 要求每个 artifact 的 SHA256 都已登记，而**预检自己的 stdout 日志**也被要求登记——
于是"日志的哈希"只能由"成功运行的日志字节"决定，构成不动点。两处踩坑，均已消除：

1. PowerShell 的 `>` 重定向在此机器写 **UTF-16**，日志哈希永远对不上 → 改为 Python 以**原始字节**捕获。
2. Python 文本 stdout 在 Windows 把 `\n` 翻成 `\r\n`，预测长度差 1 字节 → 预测式改用 `os.linesep`。

现由 `preflight.py --write` 先落地**预测字节**并打印哈希供登记，再 `--run` 跑真预检，最后 `--check`
断言"真字节 == 预测字节 == 已登记哈希"。三者一致（`4e73ff6e…2aa02be`），不让任何一处糊过去。

