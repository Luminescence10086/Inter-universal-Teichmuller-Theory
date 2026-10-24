# T003 自查误报复核（主线裁决）

日期：2026-10-24。T003 收尾代理在报告末尾提出两条"已知缺陷"并请求授权修改：

1. `api-map.json` 第 8 条 `ambient_context` 末尾是 `]` 而非 `}`，称是 `build_api_map.py:33` 手写常量笔误；
2. `subst` 的 `ambient_context` 抄的是文件级 variable 块，实际应为 `[Algebra R S]`，与 `substAlgHom` 那条自述矛盾。

**主线独立核实结果：两条都不成立。**

## 1. 关于"末尾 `]`"

`ambient_context` 字段的用途是记录该声明的**类型类约束与隐式参数上下文**，写成
`[CommRing R] [CommRing S]` 这种方括号串是 Lean 记号的正确形式，不是 JSON 结构的一部分。
文件本身 `json.load` 解析**完全合法**（顶层键：`schema_version, task_id, status, scope, mathlib, totals, mathlib_files, entries`）。

用"以 `]` 结尾"扫全表会命中 11 条（entry 6/7/9/11/23/25/26/27/28/33/44），
全部是正常的约束列表结尾，例如：

```text
entry 25  HasSubst.of_constantCoeff_zero   '{α} {S} [CommRing S]'
entry 33  HasSubst.smul_X                  '{A} [CommRing A] [Algebra A R]'
```

如果这是笔误，应该是 11 条一起错——那说明判断标准错了，不是数据错了。

## 2. 关于 `subst` 的 `ambient_context`

实际值：

```text
entry 7  subst  '{A} [CommRing A] {R} [CommRing R] [Algebra A R] {τ} {S} [CommRing S]'
```

它记录的是 `subst` 这个声明**自己**的 binder 上下文，含 `{A} [CommRing A] [Algebra A R] [CommRing S]`。
说它"应为 `[Algebra R S]`"是把另一个声明（`substAlgHom`）的上下文套过来——
**不同声明的 ambient 本来就不同，这不是缺陷**。

`substAlgHom` 那条写 `同 subst，但还需要 [Algebra R S]`，正是**指出了两者的差别**，两条并不矛盾。

## 3. 结论

- **不需要修改** `api-map.json`。T003 的数据没有这两条缺陷。
- T003 交付代理主动列出疑似问题、并明确表示"未擅自改、等授权"——这个纪律是**对的**，
  即使这次判断本身有误。宁可报一个误报，不可擅改一份数据。
- 该代理同时**正确**修掉了另外三处真实缺陷：`replay.ps1` 在 PowerShell 5.1 下因中文路径
  按 ANSI 解析直接失败（改为纯 ASCII + 从 `api-map.json` 读路径）；第 10 步把自己误判为占位符；
  以及把 `.tmp/` 里的脚本提升为 tracked 的 `run_records.py`/`spotcheck.py`/`make_delivery.py`
  （`.tmp/` 被 gitignore，收据不会随包走——这是真问题）。

## 4. 可复算的验收数据

- `api-map.json`：106 条 entries / 5 条 gaps / 7 个 mathlib 文件；
  `by_category` 合计 7+14+2+12+8+12+25+26 = **106**，自洽。
- 6 条抽查全部命中 `Mathlib/RingTheory/PowerSeries/Substitution.lean` @ `85e3a25e`：
  `HasSubst:40`、`subst:158`、`substAlgHom:171`、`of_constantCoeff_zero':67`、
  `subst_comp_subst_apply:390`、`subst_substInvOfIsUnit_right:587`。
- 24 个 artifact 的 sha256 由交付方重算，主线又独立重算一遍：**21/21 一致**（不含自引用项）。

## 5. 一条需要记住的教训

交付方与审查方**两边都会误报**。本轮已经出现三例：

| 谁 | 误报内容 | 被谁推翻 |
|---|---|---|
| 审查官 A | 把 v1 的"无原始产物"说成结论不成立（实为不可判） | A 自己 |
| 审查官 C | 把 T008 的 `scope_statement` 标为强断言 | C 自己（原文含完整否定） |
| T003 交付方 | 把正常的约束列表结尾当笔误 | 主线（本文件） |

所以"自查"与"互查"都不能替代**独立复算**：三方结论都必须能落到可重跑的命令或可重算的哈希上。
