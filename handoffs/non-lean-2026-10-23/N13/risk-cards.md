# N13 风险卡：声明、假设与原文忠实性的静态审查

审查对象：5 个关键声明（每文件一个）+ 1 处收据块。**只读文本**：未运行 Lean/Lake/Lean LSP，未打开编辑器。
**文本搜索 ≠ 公理闭包审计**：本件只统计 `sorry / axiom / set_option` 的文本出现，以及 `#print axioms` 行的位置，
没有重算任何依赖闭包。核心 GAP 保持 OPEN。

标注约定：`SOURCE_FACT`＝源码里可逐字核对的文本事实；`JUDGEMENT`＝我的逻辑判断，未经编译器确认；
`UNVERIFIED_MATH`＝需要后续形式化的命题。

---

## C1 — 「读数非零」被写成「非扭」｜`JUDGEMENT` + `SOURCE_FACT`

- 位置：`candidates/core-transport/H3Synthesis.lean:161-163`，`:226-227`。
- 原文（161-163）：“The hypothesis `reading R x ≠ 0` is **exactly the non-torsion condition**: it is what makes
  the cancellation available”；原文（226-227）：“The trivial reading on the free group: every element reads `0`.
  Its kernel is everything, so **no probe whatsoever is non-torsion for it**.”
- 疑点：`reading` 是**任意**加法读数（`R : G →* Multiplicative ℚ_[3]`），不是对数。`reading R x ≠ 0` 只在
  读数于 `x` 的循环子群上单射时才等价于「`x` 非扭」。同一文件里的 `trivialReading` 与 `probeOne`（自由群生成元，
  无限阶）恰好给出反例形状：无限阶元素读数也为 0。`SOURCE_FACT`：那两段 docstring 逐字如此；
  `JUDGEMENT`：「exactly」这个措辞不成立，除非把读数单射性写成假设。
- 建议改法：把 “non-torsion condition” 换成 “non-vanishing reading”，并补一句“只有在读数于 `⟨x⟩` 上单射时才
  等价于非扭”；或另加一条定理 `reading_injective_on_cyclic_of_ne_zero`（需要额外假设）。
- 后续验证需求：形式化该等价所需的最小假设；检查 W9 与 W10 的 docstring 是否也用了同一措辞。

## C2 — 量词覆盖到「读数无意义」的探针｜`SOURCE_FACT` + `JUDGEMENT`

- 位置：`ExponentUniqueness.lean:288-290`（`exponent_determined`），定义在 `candidates/core-transport/CoreTransport/Basic.lean:9-10`。
- 原文：`theorem exponent_determined (M N : ℕ) (h : ∀ x : ℚ_[3], localLog (x ^ M) = localLog (x ^ N)) : M = N`；
  `def localLog ... := ∑' n, (-1)^n * (x-1)^(n+1)/(n+1)`。
- 疑点：`∑'` 在不可和时按定义取 `0`。于是凡 `‖x^M - 1‖ ≥ 1` 或 `‖x^N - 1‖ ≥ 1` 的探针处，两边都是 0，
  假设**自动成立**。`SOURCE_FACT`：定义与陈述如此；`JUDGEMENT`：该假设比字面读起来弱得多，
  读者容易把它当作“所有探针的读数都相等”。
- 建议改法：把假设收窄到 `‖x - 1‖ < 1`（或直接只对 `x = 4` 陈述，正如证明实际用的那样），
  并在 docstring 里点明“发散的探针处两边都是 0，因此不提供信息”。
- 后续验证需求：若收窄假设，`power_reading_injective_on_probe` 可原样复用；不需要新数学。

## C3 — 归一化恒等式只在 `hAct` 下成立，而索引文字写成「落地」｜`SOURCE_FACT` + `JUDGEMENT`

- 位置：`LabelNormalization.lean:165-169`（`averageOverLabels_eq_averageOverOrbit`，假设 `hAct : Function.Bijective (fun g : G => g • base)`）；
  文件自己在 `:84` 与 `:224` 说明“这条恒等式在一个方向上刻意很弱”“标签集不是轨道时 `hAct` 失败”；
  索引文件 `research/core-backward-2026-10-23/PATH.md:35` 把 W12 概括为「M-iii 落地」。
- 疑点：`SOURCE_FACT`：恒等式确实以 `hAct` 为假设；`JUDGEMENT`：`PATH.md` 的「落地」没有携带 `hAct`，
  而原始归一化恰恰不是“标签集＝轨道”的情形，故此概括偏强。
- 建议改法：`PATH.md:35` 改为「M-iii 的**条件性**落地：仅当标签集就是轨道时两条平均相等」，或直接引 `:84` 的自述。
- 后续验证需求：不需要新的形式化；只需索引层措辞收敛。

## C4 — 「不是同义反复」这一自评不成立｜`JUDGEMENT`

- 位置：`EtaComparison.lean:293-296`（`in_orbit_iff_exists_iso_in_family` 的 docstring），`:311`。
- 原文：“the right-hand side is *not* a mere restatement, because the family is indexed by the group and the orbit
  of a member of the family is the orbit of the base scalar”。
- 疑点：`orbitFamily H c₀ s = s • c₀`，任一成员的轨道都等于 `c₀` 的轨道，因此“存在成员的轨道含 q”与
  “存在成员等于 q”在构造上就是同一件事——`eta_eq_iff_inOrbit` 一步即可互推（证明也确实只有 `rw` + 两行）。
  `JUDGEMENT`：该自评把一个定义的直接后果说成了内容。
- 建议改法：删去 “not a mere restatement”，改为“这是一个重写：两者由 `orbitFamily` 的定义互相翻译”。
- 后续验证需求：无（属措辞层面）。

## C5 — 收据块重复，且注释断言与文件内容矛盾｜`SOURCE_FACT`

- 位置：`TransitionCompatibility.lean:632-633` 的注释与 `:634-637` 的 4 条 `#print axioms`；
  同样的 4 条已在 `:593-596` 出现。
- 原文（632-633）：“audit completion (main line): the four below were declared in the file but **absent from the
  report list**, so the first strict check flagged them as un-audited. No proof was changed.”
- 疑点：`SOURCE_FACT`：`PresentationChain.{stepInv_step, relativeInput_mem, reading_hasSum, reading_is_limit_of_algorithm}`
  这 4 条已是 `:593-596` 的一部分，全文共 54 条 `#print axioms`，其中 4 条重复。因此“absent from the report list”
  对当前文件为假（可能是旧版布局留下的注释）。
- 建议改法：删掉 `:634-637` 的重复 4 条并把注释改成“已在 :593-596 覆盖”，或保留注释但改成“曾缺失，现已含在上一块”。
- 后续验证需求：不需要；但要确认是否有下游脚本按行号解析这份收据（若有，行号会移位）。

## C6 — 已核对、未发现问题：`comparison_well_defined` 的假设不是结论的伪装｜`SOURCE_FACT`

- 位置：`H3Synthesis.lean:206-217`。
- 陈述：`(hu : reading R u = 0) (hM : M ≠ 0) → reading R (u * x^M) / M = reading R x`。
- 核对：`hu` 是**输入**条件（twist-free），结论是 `x` 的读数可从除回后的结果复原；文件在 `:288-301` 另给
  “`hu` 不成立时结论为假”的具体数字反例，因此这不是把结论塞进假设。`JUDGEMENT`：无风险。
- 唯一要带走的东西：`hM : M ≠ 0` 是除法非零性条件，下游引用该定理时**必须一并携带**；不携带时在 `M = 0` 处直接假。
  这已记入 `declarations.csv` 的 `needs` 列。

## C7 — 未审的项目（明确留空）

- 未审 Mathlib 侧任何声明；未审 `Reconstruction/`、`Cor312/`、`Concrete/` 等外部仓库文件；
  未重算任何 `#print axioms` 的真实依赖闭包；未核对三标准公理之外是否有 `sorryAx`（只做了文本计数，五文件均为 0）。
- 静态「没发现问题」**不等于**形式化通过；本件不产生任何准入。
