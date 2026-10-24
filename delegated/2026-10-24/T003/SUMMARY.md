# T003 · 平方代换（PowerSeries substitution）API 地图

状态：`RESEARCH_ONLY`（只读检索报告；无 Lean 构造、无编译、无编辑器准入；不触碰主线源码 / Boundary / fact-tree）
日期：2026-10-24　任务卡 SHA256：`55edaf3d8f47973e68772a18296a56ca3c1d711f1e0f259078d66f9e3cabcbdb`
baseline.json SHA256：`e24e6801c2eac58f7d97cfe5f3f7a95deeaf05852231006a0085290eecd126cf`
Mathlib（只读）：`C:\Users\18746\Desktop\数竞屠宰场\.lake\packages\mathlib` @ `85e3a25e006c35636f0e53b0e9296caca2685bc0`（`git rev-parse` 实测，与 baseline.json `mathlib.commit` 一致）

## 目标

在固定 Mathlib 中给出 substitution / 零常数项 / 单位映射 / 复合四类 API 的准确声明名、文件、完整类型与最短调用草案；未找到的给检索词与检索范围。

## 实际结果

**命中条目 106 条**（`api-map.json` 的 `entries`，全部逐条从固定 commit 抽取、无 placeholder；`REPLAY` 断言 `entries >= 100`、`gaps == 5`），四类完整覆盖；**复合（composition）类的"封闭"部分命中，"逆/群"部分为 typed gap**。

| 类别 | 命中 | 关键结论 |
|---|---|---|
| A. substitution 主 API | 14 | 单变量在 `PowerSeries` 命名空间，实现全部下放到 `MvPowerSeries` |
| B. 零常数项 / 可代入谓词 | 14 | 谓词是 `IsNilpotent (constantCoeff ·)`，**不是** `= 0`；零常数项只是充分条件 |
| C. 单位映射 | 8 | `isUnit_iff_constantCoeff` 是唯一双向桥；无 `Rˣ ≃* (R⟦X⟧)ˣ` |
| D. 复合 | 25 | `subst` 可复合（`subst_comp_subst_apply`）；逆代换 `substInvOfIsUnit` 存在但**无群结构、无 `SubstEquiv`** |
| A2/B2/D2/E 系数式、常数保持、逆代换、辅助 | 45 | 系数式右侧是 `finsum`；逆代换两侧等式齐全但无群包装 |

### 最关键的六个声明

1. `PowerSeries.HasSubst (a : MvPowerSeries τ S) : Prop` := `IsNilpotent (MvPowerSeries.constantCoeff a)` — `RingTheory/PowerSeries/Substitution.lean:40`
2. `PowerSeries.subst (a : MvPowerSeries τ S) (f : PowerSeries R) : MvPowerSeries τ S` — 同文件 `:158`
3. `PowerSeries.substAlgHom (ha : HasSubst a) : PowerSeries R →ₐ[R] MvPowerSeries τ S` — `:171`
4. `PowerSeries.HasSubst.of_constantCoeff_zero' (ha : PowerSeries.constantCoeff a = 0) : HasSubst a` — `:67`（**"平方代换"落地要的那一条**）
5. `PowerSeries.subst_comp_subst_apply (ha) (hb) (f) : subst b (subst a f) = subst (subst b a) f` — `:390`
6. `PowerSeries.subst_substInvOfIsUnit_right (hP : P.constantCoeff = 0) : P.subst (substInvOfIsUnit P hP') = X` — `:587`

### 准确前提（易错点，逐条实测）

- `HasSubst` 的可代入性是**幂零**常数项。系数环既约（`IsReduced`）时幂零⇒零，才退化为 `constantCoeff = 0`（`IsNilpotent.eq_zero`，`Algebra/GroupWithZero/Basic.lean:202`，本版实测核对）。
- `subst` 在**不满足** `HasSubst` 时不是垃圾值：`MvPowerSeries.subst` 定义即为 `eval₂ (algebraMap _ _) a f`（`MvPowerSeries/Substitution.lean:190`），退化情形给定 0。
- `substAlgHom` 的 `→ₐ[R]` 需要 `[Algebra R S]`（`Substitution.lean:33`）；一旦 `τ` 非空就有实例冲突风险，单变量 `τ = Unit` 时 `S = R` 走 `Algebra R R`。
- `subst_substInvOfIsUnit_right/left` 要求 **两条**：`P.constantCoeff = 0` 且 `IsUnit (P.coeff 1)`；`substInv`（`Invertible` 版）要求 `[Invertible (coeff 1 P)]`。
- `coeff_subst'` / `constantCoeff_subst` 的右侧是 **`finsum`**（无限和），不是 `Finset.sum`；要真算系数必须再配 `coeff_subst_finite`。

## 是否推进首个缺箭头

否。本卡是纯检索（`SOURCE_OR_ENGINEERING`，`RESEARCH_ONLY`），不产生数学断言、不新增 Lean 声明、不进入 fact-tree。

## 未解决内容（OPEN，见 `api-map.json` 的 `gaps`）

1. **无 `PowerSeries.comp` 这一操作名**。复合一律经 `subst`。若下游代码写 `f.comp g` 会直接 unresolved identifier。
2. **无 `SubstEquiv` / 代换群**。全 Mathlib `substEquiv|SubstEquiv` 零命中。可逆代换只有单向见证 + 一条唯一性（`eq_substInvOfIsUnit_of_subst_eq_X`），**没有** `X ⟦substInvOfIsUnit P hP'⟧` 的反向等式、没有 `MulEquiv`、没有 `Subgroup`。
3. **无 `Rˣ ≃* (R⟦X⟧)ˣ`**。单位与常数项之间仅有 `isUnit_iff_constantCoeff`（双向 `IsUnit`）与 `Unit_of_divided_by_X_pow_order`（`k⟦X⟧ → k⟦X⟧ˣ`，需 `Field`）。从 `h : IsUnit (constantCoeff φ)` 造出 `φ` 的 unit 需要 `IsUnit.unit` + `invOfUnit` 手工拼装，无现成引理。
4. **无 q-展开 / theta / Tate 参数层**。`TateParameter|thetaFunction|ThetaGroup` 零命中；`qExpansion` 只出现在 `NumberTheory/ModularForms/*`，与形式幂级数代换无关。若主线要"q 平移下的 theta germ"，Mathlib 无对应物，需自建。
5. **代换未与 `derivative` 之外的结构联动**。链式法则存在（`derivative_subst`），但**无** `expand`/`rescale` 之外的函子性定理覆盖任意 `h : R →+* S`（`map_subst` 只覆盖系数环映射）。

## 检索方法与可复现性

- 主工具：`tools/extract.py`（逐声明抓取源码块，不改 Mathlib）；负结果与正对照全部由 `tools/verify_gaps.py` 机器化重跑（G1–G5，结果见 `evidence/gapcheck.json`）。
- 全部 **7** 个被读取文件的 SHA256 记录在 `api-map.json` 的 `mathlib_files`；`replay.ps1` 第 8 步逐条重算比对，哈希漂移即失败。
- 实际执行的 4 条命令（argv / cwd / 退出码 / 耗时 / stdout / stderr 全录）见 `delivery.json` 的 `runs` 与 `evidence/runs.json`。重跑用 `tools/run_records.py`，生成 `delivery.json` 用 `tools/make_delivery.py`，都是普通 Python、无网络、不碰主线。
- 未构建、未 `lake env lean`：固定包 `.lake/build` 无 olean（实测 `Mathlib/RingTheory/PowerSeries/Substitution.olean` 不存在），构建属重型操作且本卡不要求编译证据。故 `delivery.json` 中 `lean_run: false`、`declarations: []`。

## 声明名抽查（本版新做）

对"六个关键声明"逐条核对 `文件:行号` 原文，全部命中（脚本 `tools/spotcheck.py` → `evidence/spotcheck.json`，`all_quoted_lines_verified: true`）：

| 声明 | 文件:行 | 该行原文（截断） |
|---|---|---|
| `PowerSeries.HasSubst` | `RingTheory/PowerSeries/Substitution.lean:40` | `abbrev HasSubst (a : MvPowerSeries τ S) : Prop :=` |
| `PowerSeries.subst` | 同上 `:158` | `noncomputable def subst (a : MvPowerSeries τ S) (f : PowerSeries R) :` |
| `PowerSeries.substAlgHom` | 同上 `:171` | `noncomputable def substAlgHom (ha : HasSubst a) :` |
| `PowerSeries.HasSubst.of_constantCoeff_zero'` | 同上 `:67` | `theorem HasSubst.of_constantCoeff_zero' {a : PowerSeries S}` |
| `PowerSeries.subst_comp_subst_apply` | 同上 `:390` | `theorem subst_comp_subst_apply (ha : HasSubst a) (hb : HasSubst b) (f : PowerSeries R) :` |
| `PowerSeries.subst_substInvOfIsUnit_right` | 同上 `:587` | `lemma subst_substInvOfIsUnit_right : P.subst (substInvOfIsUnit P hP') = X := by` |

Mathlib commit 仍为 `85e3a25e006c35636f0e53b0e9296caca2685bc0`（`git rev-parse HEAD` 实测）。`replay.ps1` 第 9 步把同样 6 条作为可执行断言，重放时再核一次。

## 已知缺陷（本版实测发现，未修）

1. `api-map.json` 第 8 条（`PowerSeries.subst`）的 `ambient_context` 末尾字符是 `]`（其余条目为 `}`）——`tools/build_api_map.py:33` 手写常量里的笔误。重跑不修正，属确定性缺陷（`api-map.json` 重放后逐字节相同，已实测）。
2. `PowerSeries.subst` 与 `MvPowerSeries.subst` 的 `ambient_context` 抄的是文件级 `variable` 块（`Substitution.lean:31–35`），而 `subst` 实际声明处的实例是 `[Algebra R S]`；`substAlgHom` 那条自己已写明"—需要 `[Algebra R S]`"，两处口径不一致。
3. `SUMMARY.md` 早期版本提到 `tools/grep_queries.ps1`，该文件不存在；负结果实际由 `tools/verify_gaps.py` 机器化重跑（已在上文改正）。
4. `api-map.json` 的 `entries` 没有 `found` 字段（共 106 条 `entries` + 5 条 `gaps`）；早期 draft 里的"45 条"与 `api-map.json` 对不上，已改用可复算的口径。

## 官方预检（`check_delivery.py`，本版实跑）

命令（原样）：

```
python -B "D:\Inter-universal Teichmüller Theory\handoffs\agent-batch-2026-10-24\check_delivery.py" --delivery "D:\Inter-universal Teichmüller Theory\delegated\2026-10-24\T003\delivery.json"
```

退出码 `0`，stdout 原样：

```json
{"result": "PACKAGE_COMPLETE", "task_id": "T003", "reported_status": "RESEARCH_ONLY", "scope": "Material and hashes only. No reported command executed; mathematics, axioms, source semantics and editor observations remain unverified."}
```

stderr：空。

说明：该检查器只核材料与哈希，不执行交付代码、不检查数学语义；`PACKAGE_COMPLETE` **不等于** Lean、编辑器或核心 gap 通过。`delivery.json` 自身不在 `artifacts` 内（清单不能包含自己的 SHA256，否则与"清单里的哈希必须等于文件实际字节"自相矛盾）；其 SHA256 记在旁注文件 `evidence/delivery.self_sha256`。

旁注：核验时该 `check_delivery.py` 正被外部并发修改（14:15:50 那一版中途 `os` 未导入，抛过 `NameError`），给的是瞬时结果；上表 `PACKAGE_COMPLETE` 是对**已稳定版本**（SHA256 `c03aebe7…533c`，266 行）实跑所得。该检查器不受本任务管辖，未修改。

