# B-semantics · ROLLUP（2026-10-24 批次）

独立审查官 B（数学语义）  更新：2026-10-24  范围：`delegated/2026-10-24/` 各任务的数学断言与语义

判定档位：`PASS` / `FAIL(理由+证据行)` / `UNDECIDABLE` / `NOT_YET`（目录不存在或无可审内容）

---

## 1. 本轮结论

| 任务 | 判定 | 最硬的一条语义问题 |
|---|---|---|
| **T002** | **UNDECIDABLE**（实质 `NOT_YET`） | `.tmp/nodes.json` 与 `fact-tree/core-germ-2026-10-24.json` **逐字段完全相同**（25 节点、42 边、18 selected 全一致），字节 SHA 差异仅序列化格式。任务卡要的「18 行类型摘要」根本不存在，无 `SUMMARY.md`/`delivery.json`/`replay`。内容层面无语义缺陷。 |
| **T008** | **UNDECIDABLE**（1 条实质错误） | `letI` 论述**反向**：`ARROW-TABLE.md:87` 与 `SUMMARY.md:29` 称忘写 `letI` 会「静默落到另一个作用实例」。独立探针实测：省 `letI` 是 **hard error**（`failed to synthesize MulDistribMulAction ↥(decompositionSubgroup) (Mu n κ)`、`HSMul` 合成失败），不是静默替换。全工程只有 `Basic.lean:86`（作用群 = `Gal(Ω/K)`，**不是** `Gal(κ/k)`）与 `Decomposition.lean:140`（`def`，不入实例搜索）两处，**不存在可供误落的目标实例**。 |
| T001 T005 T066 | **NOT_YET** | 目录不存在 |
| T003 T015 T021 T049 T065 T097 | **未审（本轮）** | 目录已有内容（T003 有 `SUMMARY.md`；T097 有 `SUMMARY.md`+`delivery.json`），待下轮 |

---

## 2. T008 详情摘要（本节为下轮可复用口径）

### 五项自述核验：4 正确 / 1 反向

| # | 自述 | 判定 |
|---|---|---|
| 1 | A16 满射需 `[IsGalois F Ω]`+`[IsAlgClosed Ω]`+`[Algebra.IsIntegral k κ]`+`hres` | **正确**（`DecompositionSurjective.lean:430`、`:506-508`） |
| 2 | A12 左腿不需 `[Algebra.IsIntegral F Ω]`，A13 右腿需要 | **正确**（`Decomposition.lean:172` 才引入该 variable，在 `reduceMu_smul`:164 之后） |
| 3 | C2 是唯一实质连续性输入，只被右腿需要 | **正确** |
| 4 | `muAction` 忘 `letI` → 静默换实例 | **错误（反向）**，见上表 |
| 5 | A21 `DecompositionBridge.lean` 无 olean | **正确**（实测 `.lake/.../Boundary/` 仅 8 个 olean） |

### 23 条箭头分类：未发现错标

- 抽查 A18（反射单射）：`ReducedComparison.lean:16-20` 的 `hsurj` 是**显式参数**，用于本方块须喂 A16，
  故 A18 强度上限 = A16 —— `ARROW-TABLE.md:171,181` 已写明，**判定正确**。
  建议补一句「A16 前提不满足 ⇒ A18 **无法实例化**」（现文「强度上限」易被读成「弱化版可用」）。
- A19 标「仍为假设」：实测全工程 `reduceMu` 行中 `Injective/Surjective/Bijective/MulEquiv` 命中 **0**，**正确**。
- A22/A23 标「仍为假设」且引用逐字准确（见 §3）。

### 证据链独立复核：通过

- `ThetaGermTransport.lean` SHA `0c7af1cd…` = shard 的 `editor_observation.source_sha256`，254 行与 `last_message_line: 254` 吻合。
- `replay.ps1` 固定 5 个输入 SHA，`replay.console.log` 5 项全 `ok`。
- `logs/probe.stdout.log`（**UTF-16LE 带 BOM**，UTF-8 读会是乱码）解码后 error/warning/sorry 均 0；11 条 `#print axioms` 全为 `propext/Classical.choice/Quot.sound`。

---

## 3. 引用忠实性抽检结果（2 条，均逐字一致）

| 抽检 | 结论 |
|---|---|
| A23 / Wall (9-1) | `EtaAlg.lean:96` `structure EtaAlg`、`:108` `out`、`:123-125` `realisation`、`:173` `def Wall … : Prop`、`:169-172` 文档串末句 "**A hypothesis, never assumed.**"。T008 表述准确。**另：`wall_iff_forall`(`:183`) 是 `↔`，不是单向——T008 未把「存在性」偷换成「所有 S 不变」。** |
| A22 / S2 决策 | `EtaleTheta/README.md:294-296`「S2 (classes on points and germs) … not as a class in `H¹(Π^tp_Ÿ, Δ_Θ)`」；`KummerClass.lean:19-22`「The tempered group `Π^tp_Ÿ` is not available here (scope decision S2 …)」。行号精确命中。 |

---

## 4. 跨任务的语义模式（供后续任务复用）

1. **「源码存在 ≠ 已编译 ≠ 已验收」**：T008 对 A21 的处置是**正确范式**——源码在、SHA 对、但无 `.olean`，
   就记「仍为假设（未核）」而不记「已构造」。后续任务遇到同类情形应照此。
2. **「不在 baseline 文件清单 ／ 本任务未构建」⇒ 不得并入箭头表**：T008 对
   `decomposition_kummer_thetaGerm` 的处理（`ARROW-TABLE.md:183-192`，只作「源码读数备查」）同样正确。
3. **复制上游产物冒充交付**：T002 的 `.tmp/nodes.json` 是反例模式。**内容无错但零增量**，
   且任务卡要求的摘要缺失。判此类时须做「与既有 fact-tree 逐字段比对」，不能只看 `status` 字段自报。
4. **「强度上限 = X」是危险措辞**：当某定理的满射参数由更强前提供给时，应写
   「前提不满足 ⇒ 该定理**无法实例化**」，而非「得到弱化版」。
5. **实例/`def` 的消费方式**：`@[implicit_reducible] noncomputable def` 形式的「实例」
   **默认不参与实例合成**，故不是「会静默选错」，而是「根本合成不出来」。判此类论断须实测
   `#synth` / 省略测试，不能凭印象。

---

## 5. 未决与下一轮

- **待审**：T003、T015、T021、T049、T065、T097（目录已有内容）。优先 T003 与 T097（均已有 `SUMMARY.md`）。
- **待出现**：T001、T005、T066（`NOT_YET`）；后续新增目录按同样口径审。
- **审查边界**：本官只审数学断言与语义。`delivery.json` 字段完整性、命令 argv/退出码链条
  属 A 类/手续类审查范围，本报告不对其下结论。
