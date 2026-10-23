M2 归一化账本 — 静态定位，无 Lean / 无构建 / 无 GUI

- 27 行（`normalizations.csv`，11 列），四个单元齐备：cQ3 3 行；Remark 3.9.5(vii) Ob3/Ob4 9 行（含 Ob8 迭代 1 行）；Cor 3.12 (xi-c)/(xi-d) 6 行；Remark 3.12.2(iv)/(v) 5 行；另有 4 行同源被引定义（Prop 3.9(i)/(iii)、Remark 3.1.1(ii)/(iv)）单独成行，不与使用它的单元混算。
- **显式因子（可直接抄）只有 5 处**：Remark 3.1.1(iv) 的 `(1/N_E)·μlog_E(S)=Σ_v (1/N_v)·μlog_v(S_v)`；Remark 3.1.1(ii) 的 `[K_v:(F_mod)_v]^{-1}` 与乘积权重；Prop 3.9(i) 的 packet/procession 归一化；Ob3-2 的 M 的刻画；Ob4 的"对 M 次 tensor power 的 q-pilot 作比较"。
- **其余全是原文引用**：`det^{⊗M}` 的 M 无值（Ob3-2 只说"唯一确定"，对 N_E 是 "cf."）；Ob3-1-2 明说 "We leave the routine details to the reader"；(xi-d) 的 "[suitably normalized, with respect to j∈|Fl|]" 无公式；Prop 3.9(iii) 的 "relative to a suitable normalization" 从未写出。值一律保持未知，未自行推算任何因子。
- 局部权重、全局 degree、(xi-d) 的 j-归一化三者分列不同行，未合并为同一量（`units_or_scale` 与 `unresolved` 逐行标注）。
- 状态 STATIC_ONLY。`QUESTIONS.md` 10 项，前 4 项即"除回 tensor power 后读数是否一致"：无 M→原读数的映射（Q1）、twist 对 log-volume 无影响仅为断言（Q2）、三处 M 是否同一个 M（Q3）、det 与 localization/log-volume 的交换（Q4）。
- 排版约定：CSV 中源文片段已去掉 txt 的断行与连字符，符号按版面读法写（如 `det⊗M` → `det^{⊗M}`），未改动任何词。行号为该 txt 一基行号，印刷页＝PDF 页。
