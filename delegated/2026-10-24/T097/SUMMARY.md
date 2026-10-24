# T097 — Wall (9-1) 的量词原文台账（RESEARCH_ONLY）

状态：`RESEARCH_ONLY`。本交付是**来源核查/抄录**，不是 (9-1) 的证明，也不宣称 Corollary 3.12 或 abc。
基线：仓库 `8d60456043e30a3da79cc838d03a19b80675dc98`（`explore/correspondence`）＋ 嵌套 `reviews/core-round/external/iut` @ `f7ed1cc8ea33234ec66b1f49fb9e12212742cdcb`（工作区干净）。
未改主线源码、Boundary、fact-tree、其它任务目录。

## 1. 量词链结论

**(9-1) 的规范原文**（LANA 中期报告，PDF p.46，`LANA-interim-report-2026-07.txt` L2138–L2141）：

> Concretely, we wish to show that **there exists some suitable S such that**
> `η_q = η^anab_S`. (9-1)

即 `Q(9-1) = [D 与输入 BPS 已固定] → ∃S (η_q = η^anab_S)`。

四层顺序，逐层都在原文里有出处：

| 层 | 量词 | 内容 | 出处 |
|---|---|---|---|
| L0 | 参数（非 ∀/∃） | 初始 Θ-data；Lean 里是参数 `D`、`A` | IUT III L10498（p.173）；`EtaAlg.lean` L92、L173 |
| L1 | **先固定** | 输入 BPS（"We start with a BPS"）／`A.qBPS h₂`；固定值 `−|log q|` | LANA L2060（p.44）；`EtaAlg.lean` L135；`Rss.lean` L501 |
| L2 | **∃ iota** | Step 1：输入 BPS 与 Θ-pilot BPS 的同构；(Ind1)(Ind2) 落在此选择上 | LANA L2062（p.44）、**L2118 "after fixing"**（p.45） |
| L3 | **∃ S** | (Ind3)-选择；LANA `S ⊂ VC(I_v)`，Lean `Ind3 D` | LANA **L2123 "Once we fix S"**（p.46）、L1437（p.31）；`Ind3.lean` L213 |
| L4 | 无量词 | 目标等式 `η_q = η^anab_S` | LANA L2140–L2141（p.46）；`EtaAlg.lean` L152 |

**Lean 侧的活体顺序**（`Iut/Wall/EtaAlg.lean` L173–L175）：

```
def Wall (D : InitialThetaData.{0}) (A : Wall.EtaAlg D) : Prop :=
  ∀ (h₁ h₂ : A.Side) (_gl : BPS.Iso (A.thetaBPS h₁) (A.qBPS h₂)),
    ∃ (ι : A.Choice (A.qBPS h₂) h₁) (S : Ind3 D), A.etaAnab ι S = etaQ D
```

∀ 在外、∃ 在内，且 iota 绑在 S 之前 —— 与"先固定输入/iota，再 exists S"一致。

## 2. 硬要求核对

* **"先固定输入/iota，再 exists S"：满足**（paper + Lean 两侧）。判定依据是 L2118 的 "after fixing"、L2123 的 "Once we fix S"、以及 `EtaAlg.lean` L174 的 ∀ 位于 L175 的 ∃ 之前（`T097_audit.py` 的 `nesting_order` 检查会机械地核这两点）。
* **"存在一个 S" 未被写成 "所有 S 上不变"：满足**，三条独立证据：
  1. 原文措辞是 `exists some suitable S`（L2140），限定词 "suitable" 收窄范围；
  2. (Ind3) 的来源是**知识限制**而非不变性 —— "it is not possible to reconstruct VC(O) … **we can say** [only] that this is an adelic measurable subset … we must take into account all such subsets"（L1433–L1437，p.31）；
  3. 禁式在固定缓存里**根本不出现**：`for all S` / `for every S` / `for any S` / `any such S` / `arbitrary S` 在 LANA、IUT III、`EtaAlg.lean` 三份文件里正则命中数均为 **0**（由 audit 每次运行重扫）。
* **反例/回归**：`ChoiceExistenceRegression.lean` L34–L37 的 `existence_does_not_force_invariance` 是玩具层（Bool 索引、无 IUT 对象）的形状见证。**T097 未重编译它**，它也不是 IUT 反例。

## 3. 目标等式与允许的 S

* 等式：`η_q = η^anab_S`。Lean 里是 `A.etaAnab ι S = etaQ D`，并由 `etaAnab_eq_etaQ_iff`（L152，**iff**，故不断言任何一侧）等价于单条实数等式 `logVol D (A.out ι S) = (concreteVariantData D).qPilot.lhs`。之所以一条就够，是因为 value-group BPS 是指标实线，pilot 的像决定整个映射（`BPS.lean` L329–L340）。
* 允许的 S：LANA 是 `S ⊂ VC(I_v)`（adelic + measurable）；Lean 是 `{S // IsAdelic D S ∧ ∀ i, S i ≤ hullOf D (vcI D) i}`（`Ind3.lean` L213）。**这是 Lean 作者自陈的有意偏离**（`Ind3.lean` L32–L38、`README.md` L413–L427）。量词效果：hull 读法下候选族更大 ⇒ `∃S` 更强，不是更弱；两种读法都保持 `∃S`，都不变成 `∀S`。哪种是原论证所用，本任务**不裁定**（U3）。
* `Nonempty (Ind3 D)` 成立（`Ind3.lean` L222），只说候选类型非空，**不说**存在"合适的"S —— 后者正是 (9-1) 本身。

## 4. 逐字更正（相对本目录 v1 草稿）

v1 草稿（已改名为 `sources.v1-draft.json.superseded`）有几处把行号当成了句子，逐条更正如下（全文见 `quantifiers.json` 的 `corrected_claims`）：

1. **页码拆开**：IUT III Cor. 3.12 不是整段在 pp.173–174 —— L10498–L10506 在 **p.173**，L10509–L10528 在 **p.174**。
2. **固定输入放错了页**：v1 用 pp.173–174 支撑"输入已固定"，但 Cor. 3.12 陈述里**根本没有字母 S**（L10498–L10597 内裸大写 S 只命中 L10553/10574/10581 的 `S^{±}_{j+1}`）。真正的固定值措辞是 Step (xi-e)，在 **pp.183–184**（L11048–L11063）。
3. **v1 的转述比原文强**：L11048–L11063 说的是"使输入数据的 pilot log-volume **等于**固定值 −|log q|"这一**条件**，不是"该值在存在性讨论之前已被固定"。
4. `PATH.md` 的 54–56 / 62–66 改为逐行锚（A47/A48/A49），因为那两句跨行且中间有未引用文字。
5. Scholze–Stix 由"未带行号的旁证"降级为"**既不支持也不反对**量词顺序"（A57/A58）；T097 不裁定 SS 与 LANA 之争。
6. 补 A59（IUT II Cor. 4.10，L6996，p.158）：Cor. 3.12 自身引用它做 `"0" ↔ ⟨F_l^⋆⟩` 的认同。

## 5. 机制核验（可重放）

* `T097_audit.py`：对 `quantifiers.json` 里 **197 项**做机械核查 —— 单行锚（文件+行+needle）、页码锚（行必须落在其声称的 `PAGE n` 标记内）、区间锚（needle 必须按序出现）、全部输入 SHA256/字节数、量词顺序、∀ 必须早于 ∃、禁式正则全扫。
* 本次实际运行：`replay.ps1` → `ALL_ANCHORS_VERIFIED`，**exit 0**，stdout/stderr 见 `logs/audit.stdout.log` / `logs/audit.stderr.log`，命令与耗时见 `logs/audit.run.json`，被重放文件的 SHA 见 `logs/replay.pins.log`。
* **否定对照**：故意改坏两个 needle 后 audit 返回 `ANCHORS_FAILED`、`exit 2`、2 项失败（`logs/negative_control.log`）。故通过不是空转。

## 6. 未解决

* **U1** (9-1) 在其自身来源中未被证明："we, the LANA project, do not have a proof of (9-1) at this time"（L2282，p.49）。本任务不上调该状态。
* **U2** 归属边界：Mochizuki 原文没有"S 版"(9-1)，S 版是 LANA 的重构；Cor. 3.12 自己的措辞是 `−|log q| ∈ R_{≤−|log Θ|}` 的**成员关系**。本任务不把 S 版读回 IUT。
* **U3** (Ind3) 范围：LANA `S ⊂ VC(I_v)` vs Lean `S ⊂ hull(VC(I))`，只记录不裁定。
* **U4** η 执行的来源：`EtaAlg.out` 是裸结构字段，接口没有给出真实的、来自原文的 (iota, S) 执行。
* **U5** 本任务**未运行 Lean**（`SOURCE_OR_ENGINEERING`）；"文件里写着 X" ≠ "X 能编译"。
* **U6** `.txt` 缓存是有损抽取（字形错配，如 `S⊂VC(I v)`、连字退化成 `de铿乶ition`），故一律以"行号 + needle"锚定，不当作 PDF。

## 7. 交付物

`quantifiers.json`（主台账，含 52 条 anchors / 23 条 page_anchors / 15 条 span_anchors / 19 个输入 SHA）、`T097_audit.py`（核验器）、`replay.ps1`、`delivery.json`、`logs/`（本次实际 stdout/stderr/argv/耗时/否定对照）。
