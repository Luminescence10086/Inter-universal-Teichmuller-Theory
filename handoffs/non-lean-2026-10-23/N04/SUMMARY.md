# N04 静态摘录：原始系数环 / order / 分解 / 有限商接口

状态：`PARTIAL`。固定输入 `reviews/core-round/external/iut` @ `f7ed1cc8ea33234ec66b1f49fb9e12212742cdcb`（实测 `git rev-parse HEAD` 一致、`git status --porcelain` 干净）。只把 `.lean` 当文本读；未运行 Lean/Lake/LSP，未开 VS Code。

## 关键发现（SOURCE_FACT）

1. 任务卡点名的 `Arithmetic.lean` **不含** tensor order / maximal order / 张量代数分解 / 有限商格：全文 223 行只有 `ordp_mul`、`intValuation_residueChar`、`fiber_finite`、`sum_localDeg`、`sum_mult`、`ramIdx`/`differentIdeal` 相关结论。所需定义全在导入链下游：`ResidueField.lean → MaximalOrder.lean → Indeterminacy.lean → Integral.lean`（`LogShell.lean` 的直接 import 为 `LocalLogShell`/`ThetaAdmissible`/`Arithmetic`）。
2. tensor order：`orderSubmodule : Submodule ℤ_[p] (Tensor K (.finite p) c) := Submodule.span ℤ_[p] (integralSet p c)`（`Integral.lean:206-209`），`order` 只是同一对象的 `Set` 写法（:211-212）。docstring 称它"即 `⊗_{ℤ_p} 𝓞_{c j}` 的像"，但 Lean 中**没有**与抽象张量积环的同构声明 ⇒ 命名忠实性 `UNRESOLVED`（散文 ≠ 定理）。
3. maximal/integral order：`integral : Set (Tensor K (.finite p) c) := integralClosure ℤ_[p] (Tensor K (.finite p) c)`（`MaximalOrder.lean:181-185`）——**按定义就是 integral closure**，故 tensor order ≠ maximal order；两者只有 `order_subset_integral`（`MaximalOrder.lean:191`），严格包含或相等都没有定理。
4. 唯一的"到乘积"分解是 **Artinian 剩余域分解** `residueEquiv : Tensor K (.finite p) c ≃ₐ[Tensor K (.finite p) c] ∀ m, ResidueField p c m`（`ResidueField.lean:72-75`，经 Mathlib `IsArtinianRing.equivPi`）。它是**环级**同构（基环 = packet 自身，不是仅 ℚ_p-线性），但指标是 `MaximalSpectrum`（剩余域），**不是**局部域因子 `∏_j K_{c j}`；因子乘积分解在本仓库无签名。
5. order 在分解下的对应只是逐点判据 `x ∈ integral ↔ ∀ 𝔪, resNorm (proj x) ≤ 1`（`ResidueField.lean:193-197`）；docstring 写成"闭单位球之积"，但没有把 `(R_I)^∼` 表述为乘积环的子环像。

## 关键两条锚点（供主线快速复核）

- tensor order → `Iut/Concrete/LocalConstruct/Integral.lean:206-209`（`file_sha256`/`verbatim_sha256` 见 `signatures.csv`）
- maximal/integral order → `Iut/Concrete/LocalConstruct/MaximalOrder.lean:181-185`

## UNRESOLVED / INPUT_DRIFT

- 有限商参考格：本仓库**无** `Finite (Tensor ⧸ L)` 或商计数格定义；最接近者仅 `orderSubmodule`（ℤ_p-lattice）、`tensorLogShell`（`LogShell.lean:295-296`）、`integralAddSubgroup`（只是 `AddSubgroup`，`MaximalOrder.lean:323-324`）。
- maximal order 的**环级**分解对应（乘积环 ≅ 子环）无签名；只有逐点范数判据。
- 与原文（IUT IV Prop. 1.2、III Prop. 3.2）的忠实性：本任务不判。源码里有定义 ≠ 原文忠实性已证。
- 依赖预算：卡限"至多两个直接依赖"，实际读了 3 个定义文件（`Integral`/`MaximalOrder`/`ResidueField`）＋ `Packet.lean`（仅查 `Tensor`/`Factor` abbrev），已记入 `delivery.json.unresolved`。
- `INPUT_DRIFT`：工作区 HEAD 现为 `568e4be9f8b3e4f1d35b5c358e3f3b7836f469c2`，任务总表快照为 `1a8515d88084e5283d02ea918131c7faed38a7da`；不影响固定外部 commit 输入。

## 复核方式

- `py -3 handoffs/non-lean-2026-10-23/N04/verify_N04.py`：按行号重抽 4 条 `signature_verbatim` 与源文件逐字比对，复算 `delivery.json` 全部输入/输出 SHA256，校验状态枚举与 `source_commit`。
- `py -3 handoffs/non-lean-2026-10-23/N04/make_N04.py` 可幂等重生成 `signatures.csv`（只写本目录）。
