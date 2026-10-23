# M2 round-2 增量：任意坐标子集乘积的最小性（候选，未准入）

base `2a13a5bca589bd1100c48282ca30cf0e1e55acce` → head `e0b5294a3ef86674b14ccf18eb30949854752374`（`round2/m2`）。
只改 `candidates/orbit-quotient/{Candidates/OrbitQuotient.lean, Candidates/Axioms.lean, README.md}`；未改 bridge/fact-tree/pins/收据。

新增主定理（均在 `namespace OrbitQuotient`，公理依赖仅 `propext, Classical.choice, Quot.sound`）：
- `hull_least_coordinateProduct : U ⊆ Set.pi Set.univ S ↔ B (hullThresh Γ hΓ k) ⊆ Set.pi Set.univ S`（任意坐标子集 `S`，含 `S j = univ` 的自由坐标）。双向即任务定义“H 是含 U 的最小坐标乘积集合”：`←` 保 U ⊆ H，`→` 每个含 U 的乘积都含 H。
- `hull_minimal_from_products`：把旧的有界阈值版 `hull_minimal`（原要求 `p` 素数、`k' ≤ N`）由任意乘积版推出，证明新接口严格包含旧接口；推导不再需要上述两前提。
上一轮已提供的 `hull_minimal_coordinateProduct` / `coordinateProductHull_orbitUnion` / `coordinateProductHull_minimal` 保持原样。
σ/σ⁻¹：`permAct γ x = x ∘ γ`，`orbitUnion` 取逆像；`orbitUnion_eq_inverse_images` 证 `U = ⋃ γ∈Γ permAct γ.symm '' B k`，`mem_permAct_box` 证 `permAct γ x ∈ B k ↔ x ∈ B (j ↦ k (γ.symm j))`。
计数未变且为独立证明：`box_cardinality : |B k| = p^(∑ j, (N - k j))`；`enlargement_budget`（`|B k|·p^e = |B k'|`）、`enlargement_budget_hull`（需 `1 ∈ Γ`）；`two_three_four` 内 2、3、4 三个基数各自成支证明。

一次 Lean 检验（共 4 条命令，全部 exit 0，68.0 s，`-DwarningAsError=true`）：入口 17.3 s 零诊断、`Axioms.lean` 16.3 s（40 声明，0 error/warning）、`HullTool.lean` 16.5 s、工具生成证书 16.1 s。
Python 工具：固定小例 `two-three-four.json` exit 0（hull=(0,0)，指数 1→2）；`unittest` exit 1 —— 唯一失败项是沙箱拒绝在 `tempfile.mkdtemp` 目录内建文件（环境限制，已用固定名目录重放同一断言：exit 0）。

未解决：实际 VS Code 观察（candidate-only，须复核方/集成者做）；有限计数不等于 log-volume，全局误差与真实 seed/κ/σ 身份仍为独立义务；`hull_minimal` 与 `hull_minimal_from_products` 并存（后者更强），未删旧定理。
