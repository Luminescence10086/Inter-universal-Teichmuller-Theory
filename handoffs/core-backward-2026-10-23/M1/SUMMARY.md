# M1 — SUMMARY (arrows and endpoints inventory)

Status: **STATIC_ONLY**. Static extraction from the cached `.txt` only; no Lean, no build, no GUI.
- 28 rows in `arrows.csv`: 2 for (sQ1)/(sQ2), 5 for cQ3, 1 for cQ4, 1 for iQ5, 1 for the closed loop,
  11 for the Remark 3.10.2 diagram (3 lower + 3 upper + 4 vertical + the conjugation relation), 7 for IPL.
- The diagram is readable from the text alone: p.152, txt 9237–9301, two rows of four nodes
  (`env`, `gau`, `LGP`, `lgp`) with four upward vertical arrows, one per column. No arrows invented.
- IPL composition (p.161, txt 9863–9872) verbatim: inverses of the first two lower horizontals, then
  the first vertical, then the three upper horizontals. Its own domain/codomain are **not** stated →
  `UNRESOLVED` (Q1). Composability forces `n,m LGP → (n,◦)lgp`; recorded as inference, not as source.
- `inverse_explicitly_used=yes` only where the source says "inverses" (IPL-A/B, IPL-COMPOSITE).
  All other diagram arrows are drawn `∼→` forward. No representative was selected from any
  poly-isomorphism; no endpoint was filled in with "they ought to be the same".
- Type-connection problems visible in the text: (1) the composite is family-indexed, not an object;
  (2) rows are indexed `(n,m)` vs `(n,◦)`, so a vertical arrow changes the object's indexing while the
  diagram treats all nodes as one kind; (3) "conjugating" asserts a square-commutation but states no
  compatibility among V1–V4 and never writes the inverse; (4) the "structure poly-morphism" is an
  Aut-orbit yet the quotient is called formal/stack-theoretic; (5) the loop closes only "up to formal
  quotient indeterminacies", and `(sQ5)` afterwards forgets the Galois/unit data.
- Nothing here closes a loop or establishes pilot preservation; both remain `UNRESOLVED` by design.
