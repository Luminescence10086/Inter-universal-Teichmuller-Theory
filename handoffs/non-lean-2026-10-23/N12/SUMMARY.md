# N12 — 外部仓库增量与关键接口跟踪

状态：`STATIC_COMPLETE`（版本差异索引；不是数学审查，也没有运行外部 Lean）

## 范围
固定两个本地克隆：`reviews/core-round/external/iut`（base `f7ed1cc8` → head `188ff572`）。本次**只跟踪上一次审查
未覆盖的变更**：上一次已列明的 6 个新增 Lean 文件、5 个修改的 Lean 文件、7 个相同核心锚点，本轮不重复。

## 本轮的增量（7 项，全部机械可比）
1. `Plans/MR10Plan.md` **新增**：AbsTopIII Cor 2.7（全纯椭圆尖点化，IUT 引用的那一步）的实施计划。
2. `Iut/AutHolomorphic/README.md`：新增一句指向上面那份 MR10 计划。
3. `Iut/Multiradial/ROADMAP.md`：`Reconstruction/` 行改写——曲线在数域上的尖点惯性群现由 `Cusp/BelyiSpec.lean`
   （MR8.8）承担，Belyi 尖点化引用 [AbsTopII] Cor 3.7/3.8；并新增 `[TopSurr] Thm 4.12` 一行，
   作为 [AbsTopI] Ex 4.8(i) 里 rel-isom-DGC 的来源（对应 MR7）。
4. `Plans/MR9Plan.md`：Thm 1.9(b) 的"到几何的桥"标记为完成，依据 `Cusp/SurfacePi1.lean`、`Cusp/SurfaceGeom.lean`
   的 `exists_fhat_equiv`；并改写 pin 说明。
5. `lakefile.toml`：`pi1` 由 `7647d28` 升到 `12719c9`；`orbicurve-cores` 由 `21ce4b7` 升到 `d08559e`。
6. `lake-manifest.json`：依赖集合里出现 `curves-jacobian`（`601db27c`），`weil-curves` 仍在。
7. `scripts/shell_lint_allowlist.txt`：2026-10-23 的 shell 审计把 439 条 `new` 全部重标为 `def`（+695 行）。

## 一处必须点出的不一致（`SOURCE_FACT` + 判定）
`Plans/MR9Plan.md:125-126` 写"iut pins `curves-jacobian` a258c15、`belyi` 5f3a88e、`pi1` 12719c9"，
但同一 commit 的 `lakefile.toml` 实际钉的是 `curves-jacobian 601db27c…`、`belyi 7206d783…`。
`pi1` 一致，另外两个**不一致**。这不是数学问题，是计划文本与锁文件不同步；检索者若照计划文本引用依赖版本会引错。
