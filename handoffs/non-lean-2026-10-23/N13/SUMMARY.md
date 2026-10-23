# N13 — 声明、假设与原文忠实性的静态审查

状态：`STATIC_COMPLETE`（风险清单；**不产生**任何形式化通过）

审查 5 个关键声明 + 1 处收据块，出 **6 张卡 + 1 项「未审」说明**（`risk-cards.md`，表在 `declarations.csv`）。
只读文本：未运行 Lean/Lake/LSP，未打开编辑器；五文件的 `sorry / axiom / set_option` 文本出现次数均为 0（`SOURCE_FACT`）。

## 三条最要紧的
1. **C1**：`H3Synthesis.lean:161-163` 把「读数非零」写成「exactly the non-torsion condition」。读数是**任意**加法读数，
   该等价只在读数于 `⟨x⟩` 上单射时成立；同一文件里的 `trivialReading`（全员读 0）与无限阶生成元 `probeOne`
   正好给出反例形状。建议改成「非零读数」并把单射条件写成假设。
2. **C2**：`ExponentUniqueness.lean:288-290` 的假设量化**全部** `ℚ_[3]`，而 `localLog` 是 `tsum`（不可和取 0，
   `CoreTransport/Basic.lean:9-10`）：在发散的探针处两边都是 0，假设自动成立。假设比字面读起来弱得多。
3. **C3**：`LabelNormalization.lean:165-169` 的恒等式**以 `hAct` 为假设**，文件自己在 `:84`、`:224` 说明了这一点；
   索引文件 `PATH.md:35` 却概括为「M-iii 落地」，丢了条件。

## 其余
- **C4**：`EtaComparison.lean:293-296` 自评「不是同义反复」不成立——`orbitFamily` 让每个成员的轨道都等于 `c₀` 的轨道。
- **C5**：`TransitionCompatibility.lean:634-637` 的 4 条 `#print axioms` 与 `:593-596` 重复，且 `:632-633` 的注释
  「absent from the report list」对当前文件为假（全文 54 条，4 条重复）。
- **C6**（已核、无问题）：`comparison_well_defined` 的 `hu` 是输入条件不是伪装结论；但 `hM : M ≠ 0` 必须随引用携带。

## 未审（`UNRESOLVED`）
Mathlib 侧声明、外部仓库 `Reconstruction/Cor312/Concrete`、以及任何 `#print axioms` 的真实依赖闭包都未审；
**静态「没发现问题」不等于形式化通过**，核心 GAP 保持 OPEN。
