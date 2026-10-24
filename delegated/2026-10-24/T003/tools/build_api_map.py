"""T003: assemble api-map.json from the verbatim signature dump plus curated metadata.

Design notes
------------
* Signatures are NEVER retyped. They are copied verbatim from `.tmp/sigs.txt`, which
  sigs.py produced by cutting proof bodies off the Mathlib source blocks.
* The curated part is the REGISTRY below: category, ambient typeclass context,
  shortest call draft, caveats. `dir` ("PowerSeries" | "MvPowerSeries") plus
  `file`/`line`/`name` must match a dump key exactly, otherwise the build fails loudly
  (no silent dropping).
* Negative results (declarations that do NOT exist) live in GAPS and are asserted
  against. They carry the exact grep terms and search scope so the claim is auditable.
"""
import hashlib
import io
import json
import os
import sys

MATHLIB = r'C:\Users\18746\Desktop\数竞屠宰场\.lake\packages\mathlib'
MATHLIB_COMMIT = '85e3a25e006c35636f0e53b0e9296caca2685bc0'

PS = 'Mathlib/RingTheory/PowerSeries/'
MV = 'Mathlib/RingTheory/MvPowerSeries/'

# ---------------------------------------------------------------------------
# Registry: one row per retrieved declaration.
# (dir, file, line, name, category, ctx, draft, notes)
# ---------------------------------------------------------------------------
REGISTRY = [
    # ===== A. substitution core =====
    ('PowerSeries', 'Substitution.lean', 158, 'subst', 'A_substitution_core',
     '{A} [CommRing A] {R} [CommRing R] [Algebra A R] {τ} {S} [CommRing S]',
     'PowerSeries.subst (a : MvPowerSeries τ S) (f : R⟦X⟧) : MvPowerSeries τ S\n'
     '-- 平方代换：a := PowerSeries.X ^ 2，即 PowerSeries.subst (PowerSeries.X ^ 2) f',
     '单变量→多变量。a 不满足 HasSubst 时不报错：MvPowerSeries.subst 定义体即 '
     'eval₂ (algebraMap _ _) a，退化情形给 0，不会静默给出错误等式。'),
    ('PowerSeries', 'Substitution.lean', 171, 'substAlgHom', 'A_substitution_core',
     '同 subst，且需要 [Algebra R S]',
     'PowerSeries.substAlgHom (ha : HasSubst a) : R⟦X⟧ →ₐ[R] MvPowerSeries τ S',
     '有 ha 才成 AlgHom。其 coe 由 coe_substAlgHom 给出。'),
    ('PowerSeries', 'Substitution.lean', 175, 'coe_substAlgHom', 'A_substitution_core',
     None, 'rw [PowerSeries.coe_substAlgHom]   -- ⇑(substAlgHom ha) = subst a', None),
    ('PowerSeries', 'Substitution.lean', 162, 'subst_def', 'A_substitution_core',
     None, 'rw [PowerSeries.subst_def]   -- rfl 级展开到 MvPowerSeries.subst', None),
    ('PowerSeries', 'Substitution.lean', 191, 'subst_add', 'A_substitution_core', None, None, None),
    ('PowerSeries', 'Substitution.lean', 212, 'subst_mul', 'A_substitution_core', None, None, None),
    ('PowerSeries', 'Substitution.lean', 208, 'subst_pow', 'A_substitution_core', None, None, None),
    ('PowerSeries', 'Substitution.lean', 324, 'subst_X', 'A_substitution_core',
     None, None, 'subst a X = a —— 代换的定义性公理。'),
    ('PowerSeries', 'Substitution.lean', 322, 'subst_C', 'A_substitution_core',
     None, 'rw [PowerSeries.subst_C]',
     '注意书写方向：(C r).subst a，subst 的 a 是隐式由 section 变量给出的。'),
    ('PowerSeries', 'Substitution.lean', 297, 'X_subst', 'A_substitution_core',
     None, 'rw [PowerSeries.X_subst]   -- f.subst X = f', '@[simp]'),
    ('PowerSeries', 'Substitution.lean', 317, 'subst_coe', 'A_substitution_core',
     None, None, '多项式层与 Polynomial.aeval 对表。'),
    ('PowerSeries', 'Substitution.lean', 305, 'substAlgHom_coe', 'A_substitution_core', None, None, None),
    ('PowerSeries', 'Substitution.lean', 313, 'substAlgHom_X', 'A_substitution_core', None, None, None),
    ('PowerSeries', 'Substitution.lean', 184, 'substAlgHom_eq_aeval', 'A_substitution_core',
     '需要 [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]',
     None, '文件自带 docstring：不鼓励使用，会引入拓扑导致 awkward comparison。'
           '日常复合请走 subst_comp_subst_apply 而非此条。'),

    # ===== A2. coefficient formulas =====
    ('PowerSeries', 'Substitution.lean', 236, 'coeff_subst', 'A2_coefficient_formula',
     None, None,
     '右侧是 finsum（无限和）而非 Finset.sum；要真正算系数必须再配 coeff_subst_finite。'),
    ('PowerSeries', 'Substitution.lean', 247, "coeff_subst'", 'A2_coefficient_formula',
     '{S} [CommRing S] {b : S⟦X⟧} {R} [CommRing R] [Algebra R S] {f : R⟦X⟧}',
     None, '单变量版（带撇）。同样是 finsum。'),
    ('PowerSeries', 'Substitution.lean', 253, 'constantCoeff_subst', 'A2_coefficient_formula', None, None, None),
    ('PowerSeries', 'Substitution.lean', 259, 'coeff_subst_X_pow', 'A2_coefficient_formula',
     None, 'rw [PowerSeries.coeff_subst_X_pow hk]',
     '@[simp]；k ≠ 0 是硬前提（k = 0 时等式不成立，X^0 = 1 代换是恒等）。'),
    ('PowerSeries', 'Substitution.lean', 275, 'constantCoeff_subst_X_pow', 'A2_coefficient_formula',
     None, None,
     '@[simp]；这就是"平方代换保常数项（经 algebraMap）"。k ≠ 0 必需。'),
    ('PowerSeries', 'Substitution.lean', 286, 'map_algebraMap_eq_subst_X', 'A2_coefficient_formula',
     None, None, '系数环映射 = 代入 X。'),
    ('PowerSeries', 'Substitution.lean', 329, 'map_subst', 'A2_coefficient_formula',
     '局部 omit [Algebra R S]，只需 [CommRing R] [CommRing S]', None,
     '系数环自然性：subst 与 map 交换。'),

    # ===== B. zero constant term / HasSubst =====
    ('PowerSeries', 'Substitution.lean', 40, 'HasSubst', 'B_zero_const_HasSubst',
     '{τ} {S} [CommRing S]',
     'example (a : MvPowerSeries τ S) :\n'
     '    PowerSeries.HasSubst a ↔ IsNilpotent (MvPowerSeries.constantCoeff a) := Iff.rfl',
     '**abbrev**，定义体 = IsNilpotent (constantCoeff a)。**不是** constantCoeff a = 0。'
     '幂零条件；系数环整环时幂零⇔为零（IsNilpotent.eq_zero）。'),
    ('PowerSeries', 'Substitution.lean', 43, 'hasSubst_iff', 'B_zero_const_HasSubst',
     None, None, '与 MvPowerSeries.HasSubst 的桥；依赖 Function.const Unit a。'),
    ('PowerSeries', 'Substitution.lean', 61, 'HasSubst.of_constantCoeff_zero', 'B_zero_const_HasSubst',
     '{τ} {S} [CommRing S]', None, '多变量版。'),
    ('PowerSeries', 'Substitution.lean', 67, "HasSubst.of_constantCoeff_zero'", 'B_zero_const_HasSubst',
     '{S} [CommRing S]',
     "have hf : PowerSeries.HasSubst (f : PowerSeries S) :=\n"
     "  PowerSeries.HasSubst.of_constantCoeff_zero' hf0",
     '带撇版专为 PowerSeries 避免 Unit 展开。"零常数项 ⇒ 可代换"的最小入口。'),
    ('PowerSeries', 'Substitution.lean', 78, "HasSubst.X'", 'B_zero_const_HasSubst',
     '{R} [CommRing R]', None,
     'X 自身可代换。文件注释：加此条是因为 simp 从 HasSubst.X 找不到它。'),
    ('PowerSeries', 'Substitution.lean', 81, 'HasSubst.X_pow', 'B_zero_const_HasSubst',
     '{R} [CommRing R]',
     'have hX2 : PowerSeries.HasSubst (PowerSeries.X ^ 2 : R⟦X⟧) :=\n'
     '  PowerSeries.HasSubst.X_pow (by decide : (2 : ℕ) ≠ 0)',
     '**平方代换的可代入性就是这一条。**n ≠ 0 必需：X^0 = 1，常数项为 1 非幂零。'),
    ('PowerSeries', 'Substitution.lean', 96, 'HasSubst.zero', 'B_zero_const_HasSubst',
     None, None, 'MvPowerSeries 目标下的 0 可代换。'),
    ('PowerSeries', 'Substitution.lean', 101, "HasSubst.zero'", 'B_zero_const_HasSubst',
     None, None, 'PowerSeries 版（带撇）。'),
    ('PowerSeries', 'Substitution.lean', 106, 'HasSubst.add', 'B_zero_const_HasSubst',
     '需要 {f g : MvPowerSeries τ R}', None, None),
    ('PowerSeries', 'Substitution.lean', 116, 'HasSubst.mul_right', 'B_zero_const_HasSubst',
     None, None,
     '命名反直觉：mul_right 证的是 HasSubst (g * f)，即"被乘侧"。'
     '姊妹 HasSubst.mul_left (:111) 证 HasSubst (f * g)。'),
    ('PowerSeries', 'Substitution.lean', 138, 'HasSubst.smul_X', 'B_zero_const_HasSubst',
     '{A} [CommRing A] [Algebra A R]', None, None),
    ('PowerSeries', 'Substitution.lean', 142, "HasSubst.smul_X'", 'B_zero_const_HasSubst',
     None, None, '单变量版。'),
    ('PowerSeries', 'Substitution.lean', 145, 'HasSubst.eventually_coeff_pow_eq_zero',
     'B2_constant_preservation', '{A} [CommRing A] {f : A⟦X⟧}', None,
     '幂零的"最终消失"形式；是 coeff_subst / derivative_subst 里 finsum 有限化的引擎。'),
    ('PowerSeries', 'Substitution.lean', 280, 'constantCoeff_subst_eq_zero', 'B2_constant_preservation',
     None, None,
     '需要 a 与 f 两条零常数项；返回的是 MvPowerSeries.constantCoeff。'),

    # ===== C. unit maps =====
    ('PowerSeries', 'Inverse.lean', 111, 'isUnit_iff_constantCoeff', 'C_unit_maps',
     '{R} [Ring R]（section Ring, :47-124）',
     'have hu : IsUnit (φ.constantCoeff) := PowerSeries.isUnit_iff_constantCoeff.mp hφ',
     '**唯一双向桥**：IsUnit φ ↔ IsUnit (constantCoeff φ)。'),
    ('PowerSeries', 'Basic.lean', 425, 'isUnit_constantCoeff', 'C_unit_maps',
     '{R} [Semiring R]（section Semiring, :75-512）', None,
     '单向（IsUnit φ → IsUnit (constantCoeff φ)）；已被 isUnit_iff_constantCoeff 覆盖，'
     '一般用 iff 版。'),
    ('PowerSeries', 'Inverse.lean', 84, 'invOfUnit', 'C_unit_maps',
     '{R} [Ring R]（section Ring）',
     'PowerSeries.invOfUnit φ u : R⟦X⟧   -- u : Rˣ 指定常数项的逆', None),
    ('PowerSeries', 'Inverse.lean', 97, 'constantCoeff_invOfUnit', 'C_unit_maps',
     None, None, '@[simp]。'),
    ('PowerSeries', 'Inverse.lean', 107, 'invOfUnit_mul', 'C_unit_maps',
     None, None, '@[simp]；需 h : constantCoeff φ = u。'
                '姊妹 mul_invOfUnit (:102) 给 φ * invOfUnit φ u = 1。'),
    ('PowerSeries', 'Inverse.lean', 157, 'invOfUnit_eq', 'C_unit_maps',
     '{k} [Field k]（section Field, :126-257）', None, '需 constantCoeff φ ≠ 0。'),
    ('PowerSeries', 'Inverse.lean', 228, 'Unit_of_divided_by_X_pow_order', 'C_unit_maps',
     '{k} [Field k]（section IsDiscreteValuationRing 之前的 Field section）', None,
     'k⟦X⟧ → k⟦X⟧ˣ；剥掉 X^order 得到的单位。不是常数项单位。'),
    ('PowerSeries', 'Inverse.lean', 236, 'isUnit_divided_by_X_pow_order', 'C_unit_maps',
     None, None, None),

    # ===== D. composition (PowerSeries) =====
    ('PowerSeries', 'Substitution.lean', 386, 'subst_comp_subst', 'D_composition',
     None, None, '函数层：(subst b) ∘ (subst a) = subst (subst b a)。'),
    ('PowerSeries', 'Substitution.lean', 390, 'subst_comp_subst_apply', 'D_composition',
     None, 'rw [PowerSeries.subst_comp_subst_apply ha hb]',
     '**复合核心引理**：subst b (subst a f) = subst (subst b a) f。'
     '需要 ha、hb 两个 HasSubst 同时在。'),
    ('PowerSeries', 'Substitution.lean', 378, 'substAlgHom_comp_substAlgHom', 'D_composition',
     None, None, 'AlgHom 层；用 restrictScalars R 对齐标量。'),
    ('PowerSeries', 'Substitution.lean', 382, 'substAlgHom_comp_substAlgHom_apply', 'D_composition',
     None, None, None),
    ('PowerSeries', 'Substitution.lean', 371, 'HasSubst.comp', 'D_composition',
     '{R} [CommRing R] [Algebra R S] {υ} {T} [CommRing T] [Algebra R T] [Algebra S T]', None,
     '可代入性在复合下封闭：HasSubst (substAlgHom hb a)。'),
    ('PowerSeries', 'Substitution.lean', 344, 'le_order_subst', 'D_composition',
     None, None, '阶的下界：a.order * f.order ≤ (f.subst a).order。'),
    ('PowerSeries', 'Substitution.lean', 359, "le_order_subst_left'", 'D_composition',
     None, None, '零常数项时 φ.order ≤ (φ.subst f).order。'),
    ('PowerSeries', 'Substitution.lean', 364, "le_order_subst_right'", 'D_composition',
     None, None, None),
    ('PowerSeries', 'Substitution.lean', 402, 'rescale_eq_subst', 'D_composition',
     None, 'rw [PowerSeries.rescale_eq_subst]',
     'rescale r f = subst (r • X) f —— 线性代换是 subst 的特例。'),
    ('PowerSeries', 'Substitution.lean', 407, 'rescaleAlgHom', 'D_composition', None, None, None),
    ('PowerSeries', 'Substitution.lean', 622, 'subst_tsum', 'D_composition',
     '需要 [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]',
     None, None),
    ('PowerSeries', 'Substitution.lean', 627, 'summable_subst', 'D_composition',
     '同上拓扑前提', None, None),

    # ===== D. composition (MvPowerSeries backing) =====
    ('MvPowerSeries', 'Substitution.lean', 78, 'HasSubst', 'D_composition',
     '{σ} {A} [CommSemiring A] {R} [CommRing R] [Algebra A R] {τ} {S} [CommRing S] '
     '[Algebra A S] [Algebra R S] [IsScalarTower A R S]',
     None, '**structure**（非 abbrev）：字段 const_coeff 与 coeff_zero。'),
    ('MvPowerSeries', 'Substitution.lean', 155, 'hasSubst_of_constantCoeff_zero', 'D_composition',
     None, None, '[Finite σ] 必需。'),
    ('MvPowerSeries', 'Substitution.lean', 190, 'subst', 'D_composition',
     None, 'PowerSeries.subst_def 展开到此', '定义体就是 eval₂ (algebraMap _ _) a。'),
    ('MvPowerSeries', 'Substitution.lean', 196, 'subst_eq_eval₂', 'D_composition',
     '需要 [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]',
     None, '进入 API 的正式入口：把 subst 归约为 eval₂（不依赖具体 uniformity）。'),
    ('MvPowerSeries', 'Substitution.lean', 210, 'substAlgHom', 'D_composition', None, None, None),
    ('MvPowerSeries', 'Substitution.lean', 229, 'coe_substAlgHom', 'D_composition', None, None, None),
    ('MvPowerSeries', 'Substitution.lean', 235, 'subst_self', 'D_composition',
     None, None, 'subst X = id。'),
    ('MvPowerSeries', 'Substitution.lean', 310, 'coeff_subst', 'D_composition', None, None,
     'finsum 形式，多元版本。'),
    ('MvPowerSeries', 'Substitution.lean', 319, 'constantCoeff_subst', 'D_composition', None, None, None),
    ('MvPowerSeries', 'Substitution.lean', 324, 'constantCoeff_subst_eq_zero', 'D_composition',
     None, None, None),
    ('MvPowerSeries', 'Substitution.lean', 349, 'map_subst', 'D_composition', None, None, None),
    ('MvPowerSeries', 'Substitution.lean', 429, 'IsNilpotent_subst', 'D_composition',
     None, None, '可代入性的传递：HasSubst a + 幂零常数项 ⇒ 结果幂零。'),
    ('MvPowerSeries', 'Substitution.lean', 477, 'subst_comp_subst_apply', 'D_composition',
     None, None, '多元复合：subst b (subst a f) = subst (fun s ↦ subst b (a s)) f。'),

    # ===== D2. inverse substitution =====
    ('PowerSeries', 'Substitution.lean', 455, 'substInv', 'D2_inverse_substitution',
     '(P : R⟦X⟧) (hP : P.constantCoeff = 0) [Invertible (coeff 1 P)]',
     None, 'Invertible 版；section substInv / section Invertible (:433-553)。'),
    ('PowerSeries', 'Substitution.lean', 444, 'substInvFun', 'D2_inverse_substitution',
     '同 section Invertible', None, '系数的递归定义。'),
    ('PowerSeries', 'Substitution.lean', 509, 'subst_substInv_right', 'D2_inverse_substitution',
     None, None, 'P.subst (P.substInv) = X。'),
    ('PowerSeries', 'Substitution.lean', 541, 'subst_substInv_left', 'D2_inverse_substitution',
     None, None, 'P.substInv.subst P = X。'),
    ('PowerSeries', 'Substitution.lean', 528, 'constantCoeff_substInv', 'D2_inverse_substitution',
     None, None, '@[simp]。'),
    ('PowerSeries', 'Substitution.lean', 531, 'HasSubst.substInv', 'D2_inverse_substitution',
     None, None, '逆代换自身可代换。'),
    ('PowerSeries', 'Substitution.lean', 565, 'substInvOfIsUnit', 'D2_inverse_substitution',
     "(P : R⟦X⟧) (hP : P.constantCoeff = 0) (hP' : IsUnit (P.coeff 1))",
     "PowerSeries.substInvOfIsUnit (P : R⟦X⟧) (hP' : IsUnit (P.coeff 1)) : R⟦X⟧",
     'IsUnit 版，比 substInv 实用（不需显式 Invertible 实例）。'),
    ('PowerSeries', 'Substitution.lean', 587, 'subst_substInvOfIsUnit_right', 'D2_inverse_substitution',
     None,
     "have h : P.subst (P.substInvOfIsUnit hP') = PowerSeries.X :=\n"
     "  P.subst_substInvOfIsUnit_right hP hP'",
     '需 hP : P.constantCoeff = 0 **且** hP\' : IsUnit (P.coeff 1) 两条。'),
    ('PowerSeries', 'Substitution.lean', 592, 'subst_substInvOfIsUnit_left', 'D2_inverse_substitution',
     None, None, None),
    ('PowerSeries', 'Substitution.lean', 598, 'eq_substInvOfIsUnit_of_subst_eq_X',
     'D2_inverse_substitution', None, None,
     '**唯一性**：任何 HasSubst Q 满足 P.subst Q = X 都等于 substInvOfIsUnit。'),
    ('PowerSeries', 'Substitution.lean', 607, 'subst_eq_X_of_subst_eq_X', 'D2_inverse_substitution',
     None, None,
     '**右逆即左逆**：单侧逆即可推出另一侧 —— 这是最接近"群结构"的地方，'
     '但仍不是 MulEquiv / Subgroup。'),
    ('PowerSeries', 'Substitution.lean', 581, 'coeff_one_substInvOfIsUnit', 'D2_inverse_substitution',
     None, None, '@[simp]；(substInvOfIsUnit P hP\').coeff 1 = hP\'.unit⁻¹。'),

    # ===== E. support =====
    ('PowerSeries', 'Basic.lean', 143, 'constantCoeff', 'E_support',
     '{R} [Semiring R]（section Semiring, :75-512）', None, None),
    ('PowerSeries', 'Basic.lean', 146, 'constantCoeff_eq', 'E_support', None, None, None),
    ('PowerSeries', 'Basic.lean', 176, 'coeff_zero_eq_constantCoeff', 'E_support', None, None, None),
    ('PowerSeries', 'Basic.lean', 313, 'constantCoeff_C', 'E_support', None, None, None),
    ('PowerSeries', 'Basic.lean', 329, 'constantCoeff_X', 'E_support', None, None, None),
    ('PowerSeries', 'Basic.lean', 450, 'map', 'E_support',
     '{S} {T} [Semiring S] [Semiring T] (f : R →+* S)（section Map, :444-489）', None, None),
    ('PowerSeries', 'Basic.lean', 457, 'map_comp', 'E_support', None, None, None),
    ('PowerSeries', 'Basic.lean', 461, 'coeff_map', 'E_support', None, None, None),
    ('PowerSeries', 'Basic.lean', 733, 'mapAlgHom', 'E_support',
     '{A} [CommSemiring A] {B} [CommSemiring B] [Algebra R A] [Algebra R B]', None, None),
    ('PowerSeries', 'Order.lean', 222, 'order_ne_zero_iff_constCoeff_eq_zero', 'E_support',
     '**section OrderZeroNeOne（:349-390）：[Semiring R] [Nontrivial R]**',
     None, '需要 [Nontrivial R]，比文件顶部 [Semiring R] 更强；引用时别漏。'),
    ('PowerSeries', 'Order.lean', 226, 'le_order_pow_of_constantCoeff_eq_zero', 'E_support',
     '同上：section OrderZeroNeOne，[Semiring R] [Nontrivial R]', None,
     '零常数项 ⇒ order 至少 n 次幂。'),
    ('PowerSeries', 'Order.lean', 300, 'constantCoeff_divXPowOrder', 'E_support',
     '需要 divXPowOrder', None, None),
    ('PowerSeries', 'Evaluation.lean', 61, 'HasEval', 'E_support',
     '{R S} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]',
     None, 'abbrev，定义体 = IsTopologicallyNilpotent a。'),
    ('PowerSeries', 'Evaluation.lean', 63, 'hasEval_def', 'E_support', None, None, None),
    ('PowerSeries', 'Evaluation.lean', 211, 'aeval', 'E_support',
     '{φ : R →+* S} (ha : HasEval a)', None, '拓扑版代入 AlgHom。'),
    ('PowerSeries', 'Evaluation.lean', 215, 'coe_aeval', 'E_support', None, None, None),
    ('PowerSeries', 'Evaluation.lean', 132, 'eval₂', 'E_support',
     '{φ : R →+* S}', None, None),
    ('PowerSeries', 'Evaluation.lean', 186, 'eval₂_eq_tsum', 'E_support', None, None, None),
    ('PowerSeries', 'Evaluation.lean', 241, 'comp_aeval', 'E_support',
     '需 [CommRing T] [UniformSpace T] [IsUniformAddGroup T] [IsTopologicalRing T] '
     '[IsLinearTopology T T] [T2Space T] [Algebra R T] [ContinuousSMul R T] [CompleteSpace T]',
     None, '拓扑完备性前提一长串；非拓扑路线请用 subst_comp_subst_apply。'),
    ('PowerSeries', 'Evaluation.lean', 228, 'aeval_unique', 'E_support', None, None, None),
    ('PowerSeries', 'Expand.lean', 33, 'expand', 'E_support',
     '{R S τ} [CommRing R] [CommRing S] (p : ℕ) (hp : p ≠ 0)',
     'PowerSeries.expand (p := 2) (by decide) : R⟦X⟧ →ₐ[R] R⟦X⟧',
     'p = 2 即"平方代换"的 AlgHom 形态。'),
    ('PowerSeries', 'Expand.lean', 36, 'expand_apply', 'E_support',
     None, 'rw [PowerSeries.expand_apply]   -- expand p hp f = subst (X ^ p) f',
     '**关键桥**：把 expand 完全归约到 subst。'),
    ('PowerSeries', 'Expand.lean', 75, 'expand_subst', 'E_support', None, None, None),
    ('PowerSeries', 'Expand.lean', 92, 'constantCoeff_expand', 'E_support',
     None, None, '@[simp]；expand 保常数项。'),
    ('PowerSeries', 'Expand.lean', 56, 'expand_X', 'E_support', None, None, '@[simp]。'),
    ('PowerSeries', 'Expand.lean', 110, 'coeff_expand', 'E_support', None, None, None),
]

# ---------------------------------------------------------------------------
# Negative results: declarations that do NOT exist in this Mathlib pin.
# Each carries the exact grep terms and the search scope actually executed.
# ---------------------------------------------------------------------------
GAPS = [
    {
        'id': 'G1',
        'claim': '不存在名为 PowerSeries.comp 的复合操作（也不存在任何 cp-alg 意义上的 comp）',
        'severity': 'blocking_for_downstream_naming',
        'grep_terms': ['^def comp', '^theorem comp_assoc', 'PowerSeries\\.comp\\b',
                       'def comp\\b.*PowerSeries'],
        'scope': 'Mathlib/RingTheory/PowerSeries/*.lean, Mathlib/RingTheory/MvPowerSeries/*.lean, '
                 'Mathlib/RingTheory/FormalGroup/*.lean',
        'result': '0 hits. 复合只能经 PowerSeries.subst 表达。对照：Polynomial.comp 存在'
                  '（Mathlib/Algebra/Polynomial/Eval/Defs.lean:381），故"多项式有 comp、'
                  '幂级数没有"是可引用的不对称事实。',
        'workaround': 'PowerSeries.subst b (PowerSeries.subst a f) '
                      '+ PowerSeries.subst_comp_subst_apply',
    },
    {
        'id': 'G2',
        'claim': '不存在 SubstEquiv / 代换群 / 可逆代换的 MulEquiv 打包',
        'severity': 'blocking_for_group_structure',
        'grep_terms': ['substEquiv', 'SubstEquiv', 'IsSubstEquiv', 'substMonoid', 'compUnit'],
        'scope': 'whole Mathlib tree (Get-ChildItem -Recurse -Filter *.lean | Select-String)',
        'result': '0 hits. 可逆代换只有单向见证（subst_substInvOfIsUnit_left/_right）'
                  '+ 唯一性（eq_substInvOfIsUnit_of_subst_eq_X）+ 单侧可推双侧'
                  '（subst_eq_X_of_subst_eq_X），**没有**打包成 Group / MulEquiv / Subgroup。',
        'workaround': '按需自建 structure 或用 subst_eq_X_of_subst_eq_X 单独取双向；'
                      '若要群结构需在 delegated 目录自建并送审。',
    },
    {
        'id': 'G3',
        'claim': '不存在 Rˣ ≃* (R⟦X⟧)ˣ 形式的单位-常数项同构',
        'severity': 'partial',
        'grep_terms': ['Units\\.map', 'unitOf', 'units_', 'ˣ'],
        'scope': 'Mathlib/RingTheory/PowerSeries/*.lean',
        'result': '只有 IsUnit 层的双向（isUnit_iff_constantCoeff）与构造性的 '
                  'invOfUnit / Unit_of_divided_by_X_pow_order。从 h : IsUnit (constantCoeff φ) '
                  '造 φ 的 unit 需手工拼 IsUnit.unit（Mathlib/Algebra/Group/Units/Defs.lean:503）'
                  '+ invOfUnit（Inverse.lean:84），无现成单条引理。'
                  '仓库内既有做法是 Units.map（见 candidates/core-kummer/Boundary/'
                  'ThetaGermTransport.lean:70 的 coordinateUnit）。',
        'workaround': 'Units.map (PowerSeries.map f).toMonoidHom u，或手工 IsUnit.unit + invOfUnit。',
    },
    {
        'id': 'G4',
        'claim': '不存在 q-展开 / theta / Tate 参数层的幂级数 API',
        'severity': 'scope_boundary',
        'grep_terms': ['qExp|q_expansion|qParameter', 'TateParameter|thetaFunction|ThetaGroup'],
        'scope': 'whole Mathlib tree',
        'result': 'qExpansion 只在 NumberTheory/ModularForms/{Bounds,Basic}.lean 出现，'
                  '与形式幂级数代换无关（是模形式的 Fourier 系数接口）。'
                  'TateParameter / thetaFunction / ThetaGroup 全部 0 hits。',
        'workaround': '这些结构在 Mathlib 无对应物；主线若要"q 平移下的 theta germ"'
                      '必须自建（不得声称为 Mathlib 已有）。',
    },
    {
        'id': 'G5',
        'claim': 'subst 与 derivative 之外的代数结构的自然性覆盖不全',
        'severity': 'informational',
        'grep_terms': ['derivative.*subst', 'subst.*derivative', 'map_subst'],
        'scope': 'Mathlib/RingTheory/PowerSeries/*.lean',
        'result': '链式法则存在（PowerSeries.derivative_subst, Derivative.lean:140）；'
                  '系数环自然性存在（map_subst, Substitution.lean:329；MvPowerSeries 版 :349）。'
                  '但 expand / rescale 之外没有通用函子性定理。',
        'workaround': '用 map_subst + expand_apply 组合。',
    },
]


def load_sigs(path):
    """Parse `### name  [relpath:line]` sections into {key: signature}."""
    text = io.open(path, encoding='utf-8').read()
    out, cur, body = {}, None, []
    for ln in text.split('\n'):
        if ln.startswith('### '):
            if cur:
                out[cur] = '\n'.join(body).strip()
            cur = ln[4:].strip()
            body = []
        elif cur is not None:
            body.append(ln)
    if cur:
        out[cur] = '\n'.join(body).strip()
    return out


def sha256_path(rel):
    p = os.path.join(MATHLIB, rel.replace('/', os.sep))
    with open(p, 'rb') as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def main():
    sigs = load_sigs(sys.argv[1])
    entries, problems = [], []

    for d, fname, line, name, category, ctx, draft, notes in REGISTRY:
        rel = (MV if d == 'MvPowerSeries' else PS) + fname
        key = '%s  [%s:%d]' % (name, rel, line)
        sig = sigs.get(key)
        if sig is None:
            problems.append('NO SIGNATURE FOR: ' + key)
            continue
        entries.append({
            'name': name,
            'full_name': ('MvPowerSeries.' if d == 'MvPowerSeries' else 'PowerSeries.') + name,
            'category': category,
            'file': rel,
            'line': line,
            'signature': sig,
            'ambient_context': ctx,
            'minimal_call_draft': draft,
            'notes': notes,
        })

    if problems:
        for p in problems:
            print(p)
        raise SystemExit('ABORT: %d registry rows did not match the dump' % len(problems))

    entries.sort(key=lambda e: (e['category'], e['file'], e['line']))
    files = sorted({e['file'] for e in entries})

    out = {
        'schema_version': 1,
        'task_id': 'T003',
        'status': 'RESEARCH_ONLY',
        'scope': 'Read-only Mathlib API retrieval. No Lean build, no editor replay, '
                 'no change to mainline sources / Boundary / fact-tree.',
        'mathlib': {
            'path': MATHLIB,
            'commit': MATHLIB_COMMIT,
            'commit_verified_by': 'git -C <path> rev-parse HEAD',
            'read_only': True,
            'built_oleans_present': False,
        },
        'totals': {
            'entries': len(entries),
            'by_category': {c: sum(1 for e in entries if e['category'] == c)
                            for c in sorted({e['category'] for e in entries})},
            'gaps': len(GAPS),
        },
        'mathlib_files': [{'path': f, 'sha256': sha256_path(f)} for f in files],
        'entries': entries,
        'gaps': GAPS,
    }
    with io.open(sys.argv[2], 'w', encoding='utf-8') as fh:
        json.dump(out, fh, ensure_ascii=False, indent=2)
        fh.write('\n')
    print('entries=%d gaps=%d files=%d' % (len(entries), len(GAPS), len(files)))
    print('by_category=' + json.dumps(out['totals']['by_category'], ensure_ascii=False))


if __name__ == '__main__':
    main()
