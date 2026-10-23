# M1 — arrow sequence in source order

Static extraction only. Source `…-2026-10-16.txt`; printed page = 1-based PDF page; numbers = `.txt` lines.
`arrows.csv` transliterates glyphs: `Fx`←`F⊩▶×μ`, `Theta`←`Θ`, `poly`←`⊼`, `sim-to`←`∼→`, `dagger-D-superscript->`←`†D>`.
Rows are `env|gau|LGP|lgp`, prefixed `n,m` (lower) or `(n,◦)` (upper).

## Arrows in source order

- **SQ1** p.139 — Frobenius-like (containing étale-like) → purely étale-like; Kummer-detachment; self-cross-referenced to the *vertical* arrows of the Remark 3.10.2 diagram.
- **SQ2** p.139 — Galois evaluation; cross-referenced to the *horizontal* arrows of that diagram. Domain/codomain unstated → UNRESOLVED.
- **CQ3-DET** pp.141–142 — O_k-stabilized hulls ∈ H → `det^⊗M(φ(P_B))` objects in the local and global Frobenioids of the codomain Fx-prime-strip, via a positive tensor power of the determinant.
- **CQ3-PULL** p.141 — pull-back morphisms in those local Frobenioids → objects with faithful `G_v` / `O^×μ_F_v` actions.
- **CQ3-POLY** p.141 — local objects carrying a "structure poly-morphism" → the hull object `det^⊗M(φ(P_B))`; the poly-morphism is the `Aut(·)`-orbit of a linear morphism.
- **CQ3-LOC** p.142 — local object's realified image ↔ localization of the global object at the corresponding primes; an isomorphism, direction not singled out.
- **CQ3-QUOT** p.142 — the pair (poly-fQ1, poly-fQ2) → "formal, or stack-theoretic, quotient" of "poly-fQ2 modulo poly-fQ1"; the quotient object is never named.
- **CQ4-LOGK** p.142 — (sQ4) vertical-shift adjustment → obtained "precisely by applying the log-Kummer correspondence"; tautologically compatible with `G_v`/`O^×μ(G_v)` isos, or with `O^×μ_F_v` allowing arbitrary log-link iterates.
- **IQ5-LOGVOL** pp.142–143 — Fx-prime-strip data → log-volumes; explicitly *forgets* local Galois groups and Frobenius-like units.
- **LOOP** pp.143–144 — q-pilot Fx-prime-strip (codomain) → through `Θ×μ_LGP`-link → through the (sQ1)/(sQ2) poly-isomorphisms [="the diagram of Remark 3.10.2", ="IPL"] → through (sQ3)/(sQ4) → a Fx-prime-strip "constrained to be subject to the q-intertwining"; closed only "up to … formal quotient indeterminacies".
- **R3102-HL1/HL2/HL3** p.152 lower row — `env→gau` (evaluation iso, [IUTchII] Cor 4.10(ii)), `gau→LGP` (tautological iso, Prop 3.7(iii)), `LGP→lgp` (tautological iso, Prop 3.7(iv)).
- **R3102-HU1/HU2/HU3** p.152 upper row — `env→gau` (étale-like evaluation iso via [IUTchII] Cor 4.6(iv),(v)), `gau→LGP` and `LGP→lgp` (natural isos, Prop 3.10(i) second display).
- **R3102-V1..V4** p.152 — four vertical arrows, each lower node → upper node *in the same column*; V1 is Prop 2.1(ii)'s Kummer iso "whose codomain includes an argument `†D>`", V2–V4 are Prop 3.10(i)'s Kummer isos.
- **R3102-CONJ** p.152 — every lower horizontal "may be constructed by conjugating the corresponding upper horizontal arrow by the relevant Kummer isomorphisms, i.e., by the vertical arrows".
- **IPL-A** — `gau→env` inverse; **IPL-B** — `LGP→gau` inverse (these are the inverses of the first two lower horizontals).
- **IPL-C** — first vertical, forward; **IPL-D/E/F** — the three upper horizontals, forward.
- **IPL-COMPOSITE** pp.160–161 — the family of "linking isomorphisms of intermediate Fx-prime-strips"; its own domain/codomain unstated.

*Inference, marked as such:* composability alone pins the composite's endpoints. IPL-C starts at lower `env`, so the inverse group must end there; A ends at lower `env` and its only in-group predecessor is B (domain: lower `LGP`). Forced chain: `n,m LGP →[B] gau →[A] env →[C] (n,◦)env →[D,E,F] (n,◦)lgp`. The source writes none of this and calls the result a *family*.

## Type-connection problems visible from the text alone

1. **The composite's type is absent.** IPL links an unnamed family of intermediate prime-strips; nothing states which, on which row, or that one fixed object is meant. A family-indexed arrow cannot be typed as a single arrow without a further choice.
2. **The two rows are indexed differently.** Lower nodes are `(n,m)`; upper nodes `(n,◦)` = the whole vertical line (txt 9313–9317), and V1's codomain "includes an argument `†D>`". So a vertical arrow changes the object's indexing while the diagram treats all sixteen nodes as one kind of "F⊩▶×μ-prime-strip" with `∼→` arrows. That the ambient category is one category for both rows is not stated.
3. **Conjugation is asserted, not derived.** R3102-CONJ is a square-commutation claim, but no compatibility among V1–V4 is stated and "the relevant" isomorphism is ambiguous across a two-column square; nor is an inverse ever written ("conjugating").
4. **"Poly-morphism" = an Aut-orbit, yet the quotient is called formal.** CQ3-POLY defines the structure poly-morphism as the `Aut(det^⊗M(φ(P_B)))`-orbit of a linear morphism — a set-level orbit — while CQ3-QUOT insists the quotients are "formal, or stack-theoretic" *as opposed to* "coarse/set-theoretic quotients". How an orbit is not itself a set-theoretic quotient is unstated.
5. **The loop closes only after data is dropped.** LOOP returns to a prime-strip "constrained to be subject to the q-intertwining" only "up to … formal quotient indeterminacies", and the next unit (iQ5) says passing to log-volumes forgets the Galois/unit data. So "closed loop" is not an equality of prime-strips, and (sQ5) is outside it.
6. **Two indeterminacy regimes for one operation.** cQ4 offers a "tautologically compatible" étale-like version with no indeterminacy and a Frobenius-like version requiring "arbitrary iterates of the log-link", with no comparison given between them.
