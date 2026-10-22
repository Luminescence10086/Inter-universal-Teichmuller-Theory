# T2 SUMMARY — STATIC_ONLY, 8 cards, no toolchain run
4 pinned repos; all HEADs match the pins, all worktrees clean ⇒ no INPUT_DRIFT. No Lean/lake/editor
command ran; "hidden premises" are static readings of the enclosing scope, not elaborator output.
8/8 cards located (`cards.md` + `cards.json`, one object per card):
1 `Iut.Wall.EtaAlg` — `Iut/Wall/EtaAlg.lean:96-125`, `realisation` 123-125
2 `Iut.Wall.EtaAlg.etaAnab_eq_etaQ_iff` — same file 151-153
3 `Iut.Wall.variant_of_wall` — same file 201-204 (scope = REOPENED `namespace Wall`, line 177)
4 `KummerTheory.restriction_kummer` — `Restriction.lean:95-98`; hidden `[Algebra.IsIntegral L ΩL]` (line 84)
5 `KummerTheory.corestriction_kummer` — `Corestriction.lean:146-148`; `L` is an `IntermediateField`;
  hidden `[IsGalois K Ω] [FiniteDimensional K L]` + 2 anonymous section instances (lines 60, 63)
6 `KummerTheory.map_section_kummer_eq_kummerValue` — `Specialization.lean:247-255`; hidden `hπ` via `include hπ in` (244)
7 `TateCurvesTheta.TateParameter.restriction_kummer_thetaUnit` — `ThetaValues.lean:284-287` (different repo!)
8 `PadicField.eq_artin_of_forall` — `ArtinUnique.lean:153-159`; hidden `[Fact p.Prime]` via `include hp in` (149)
`edges.csv`: 4 rows (2 signature_reference, 1 import, 1 proof_reference), from=referencing→to=referenced;
  NOT a closure (card3→card2 transitive, card6→4/5 via `Values.lean`, card4↔card5 only in `CorRes.lean`).
Naming inaccuracies in the handoff: (a) card 6 lacks its `KummerTheory.` prefix; (b) card 7 is not in
  `continuous-kummer-theory` at all (`git grep` exits 1) — it is in `tate-curves-theta`; (c) cards 1-3
  share one file, and card 3's scope is a reopened `namespace Wall` after `end Wall` (166).
No GAP closed; no premise claimed satisfied by the original IUT.
