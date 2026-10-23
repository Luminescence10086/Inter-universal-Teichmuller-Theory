# M1 交付摘要（round2/m1）

commit `8096774`（base `063ce7b`）；改动仅 `candidates/restricted-ledger/`：`Candidates/RestrictedLedger.lean`、`Candidates/Axioms.lean`、`README.md`。未碰主工作树源码、`fact-tree/`、pins、收据、其他任务目录；handoffs/日志不入库、未 push。

1. 强前提版保留为候选：`restricted_ledger_criterion`，末位前提 `hreal : ∀ i, ∃ x ∈ Ω, vprofile x - vprofile x₀ = b i`。
2. 新增一般 span 证书版：`restricted_ledger_span_criterion`，前提 `hspan : ∀ i, MemDiffSpanOn p Ω x₀ (b i)`（`MemDiffSpanOn Ω x₀ v := ∃ m x lam, (∀ k, x k ∈ Ω) ∧ v = ∑ k, lam k • (vprofile x k - vprofile x₀)`），即每个生成元落在实际差分生成的 ℤ-span 内；与既有 `hgen`（差分落在生成元张成内）合起来正是"生成元与差分生成同一 ℤ-子模"。
3. 从属关系已证：`memDiffSpanOn_of_realised`（hreal ⟹ hspan）、`restricted_ledger_criterion_of_combination`（强前提版＝一般版推论）；反向不成立，由 `finite_integer_span_membership_example` 的反例给出（`1 = (-1)·(2-0)+1·(3-0)`，非实际差分）。
4. Lean：只做一次尝试（上限 20 min）。`lake env lean --json -DwarningAsError=true Candidates/RestrictedLedger.lean` exit 0、24.32 s、零诊断（日志 0 字节）；`lake env lean --json Candidates/Axioms.lean` exit 0、19.66 s。
5. 公理：两个版本主定理及全部新增声明 ⊂ {propext, Classical.choice, Quot.sound}；无 `sorry`/`admit`/新公理/`native_decide`；结论未塞进结构字段。
6. 全空间特化实际只给：`full_domain_specialization` → 仅必要方向 `∀ j, w (σ j) = w j`；`full_domain_iff` → 完整 iff，但预算写作 `Σ j, w (σ j) v(a j) = 0`，与已准入 `weightedLedger_combined_invariant_iff` 的 `Σ j, w j v(a j)` 仅在权不变下相等。两者都是对该已准入定理的实例化（借道受限域），**不声称恢复全部旧判据**。
7. 未解决：无真实 IUT admissible region 及其有限生成证书（G01/G03 未关闭）；`T Ω ⊆ Ω` 仍是与"Ω 上保账"相互独立的义务；实际 VS Code 观察未做，故 candidate-only、未入 fact-tree。
