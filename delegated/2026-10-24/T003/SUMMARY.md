# T003 · 平方代换（PowerSeries substitution）API 地图

状态：`RESEARCH_ONLY`（只读检索报告；无 Lean 构造、无编译、无编辑器准入；不触碰主线源码 / Boundary / fact-tree）
日期：2026-10-24　任务卡 SHA256：`55edaf3d8f47973e68772a18296a56ca3c1d711f1e0f259078d66f9e3cabcbdb`
baseline.json SHA256：`e24e6801c2eac58f7d97cfe5f3f7a95deeaf05852231006a0085290eecd126cf`
Mathlib（只读）：`C:\Users\18746\Desktop\数竞屠宰场\.lake\packages\mathlib` @ `85e3a25e006c35636f0e53b0e9296caca2685bc0`（`git rev-parse` 实测，与 baseline.json `mathlib.commit` 一致）

## 目标

在固定 Mathlib 中给出 substitution / 零常数项 / 单位映射 / 复合四类 API 的准确声明名、文件、完整类型与最短调用草案；未找到的给检索词与检索范围。

## 实际结果

**命中条目 45 条**（`api-map.json` 中 `found: true`），前三类完整覆盖；**复合（composition）类的"封闭"部分命中，"逆/群"部分为 typed gap**。

| 类别 | 命中 | 关键结论 |
|---|---|---|
| A. substitution 主 API | 14 | 单变量在 `PowerSeries` 命名空间，实现全部下放到 `MvPowerSeries` |
| B. 零常数项 / 可代入谓词 | 11 | 谓词是 `IsNilpotent (constantCoeff ·)`，**不是** `= 0`；零常数项只是充分条件 |
| C. 单位映射 | 8 | `isUnit_iff_constantCoeff` 是唯一双向桥；无 `Rˣ ≃* (R⟦X⟧)ˣ` |
| D. 复合 | 12 | `subst` 可复合（`subst_comp_subst_apply`）；逆代换 `substInvOfIsUnit` 存在但**无群结构、无 `SubstEquiv`** |

### 最关键的六个声明

1. `PowerSeries.HasSubst (a : MvPowerSeries τ S) : Prop` := `IsNilpotent (MvPowerSeries.constantCoeff a)` — `RingTheory/PowerSeries/Substitution.lean:40`
2. `PowerSeries.subst (a : MvPowerSeries τ S) (f : PowerSeries R) : MvPowerSeries τ S` — 同文件 `:158`
3. `PowerSeries.substAlgHom (ha : HasSubst a) : PowerSeries R →ₐ[R] MvPowerSeries τ S` — `:171`
4. `PowerSeries.HasSubst.of_constantCoeff_zero' (ha : PowerSeries.constantCoeff a = 0) : HasSubst a` — `:67`（**"平方代换"落地要的那一条**）
5. `PowerSeries.subst_comp_subst_apply (ha) (hb) (f) : subst b (subst a f) = subst (subst b a) f` — `:390`
6. `PowerSeries.subst_substInvOfIsUnit_right (hP : P.constantCoeff = 0) : P.subst (substInvOfIsUnit P hP') = X` — `:587`

### 准确前提（易错点，逐条实测）

- `HasSubst` 的可代入性是**幂零**常数项。系数环整环（`IsReduced`）时幂零⇒零，才退化为 `constantCoeff = 0`（`IsNilpotent.eq_zero`，`Algebra/GroupWithZero/Basic.lean:202`）。
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

- 主工具：`tools/extract.py`（逐声明抓取源码块，不改 Mathlib）；`tools/grep_queries.ps1`（负结果检索词全录）。
- 全部 13 个被检索文件的 SHA256 记录在 `api-map.json` 的 `mathlib_files`。
- 未构建、未 `lake env lean`：固定包 `.lake/build` 无 olean（实测 `Mathlib/RingTheory/PowerSeries/Substitution.olean` 不存在），构建属重型操作且本卡不要求编译证据。
