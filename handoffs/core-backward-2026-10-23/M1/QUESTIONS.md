# M1 — open interpretive questions (handed back to the mainline)

None of these block the extraction; each is recorded so the mainline does not read an answer into
`arrows.csv` that the source does not give.

**Q1. What is the domain of the IPL composite?** Remark 3.11.1(iii) (txt 9863–9873) names only the
six constituent arrows and calls the result "the linking isomorphisms of 'intermediate'
F⊩▶×μ-prime-strips"; it never says which node the composite starts at. Composability forces the start
to be the lower `LGP` node (see `sequence.md`), and the fact that the third lower horizontal is *not*
inverted is consistent with that, but this is our inference, not the source's words. Is the intended
reading a single arrow `n,m LGP → (n,◦)lgp`, or a genuinely family-indexed arrow? The answer decides
whether K1 may treat the IPL step as one arrow at all.

**Q2. Does "conjugating" license inverse-taking?** R3102-CONJ (txt 9297–9300) says each lower
horizontal arrow "may be constructed by conjugating the corresponding upper horizontal arrow by the
relevant Kummer isomorphisms". Conjugation `g h g⁻¹` needs an inverse, but the source never writes
"inverse" here — unlike IPL, which says "the inverses of the first two lower horizontal arrows"
explicitly. Should `inverse_explicitly_used` be `yes` for this relation? We left `UNRESOLVED`.

**Q3. Are the four vertical arrows mutually compatible?** The text states each vertical arrow's
provenance (Prop 2.1(ii); Prop 3.10(i)) and asserts the conjugation relation, but never states a
relation among V1–V4 themselves. Without one, "the relevant Kummer isomorphisms" in a square spanning
two columns is ambiguous. Is such a compatibility stated in Prop 3.10(i) itself (outside the M1 slice)?

**Q4. Is the "structure poly-morphism" an orbit object or a stack quotient?** CQ3-POLY defines it as
"the Aut(det^⊗M(φ(P_B)))-orbit of a linear morphism", and CQ3-QUOT then calls the resulting quotients
"formal, or stack-theoretic/diagram-theoretic" *as opposed to* "coarse/set-theoretic quotients". The
two descriptions pull in opposite directions; the text does not reconcile them. This is the sharpest
single input to H1 (what the formal quotient retains).

**Q5. Is `(sQ5)` inside or outside the closed loop?** The loop list (txt 8672–8688) ends at
"(sQ3), (sQ4)" and the codomain is stated as a prime-strip "constrained to be subject to the
q-intertwining" — i.e. below the scalar level. IQ5 then says passing to log-volumes *forgets* the
Galois/unit data. We read `(sQ5)` as outside the loop; please confirm against Fig. 3.8 / Cor 3.12
proof, which M1 did not open.

**Q6. Which cQ4 variant is the one used downstream?** CQ4 offers a tautological étale-like version
(no indeterminacy) and a Frobenius-like version (arbitrary log-link iterates). The text does not say
which one the IPL composite or the closed loop consumes. An arrow typed from cQ4 therefore has two
possible retained-data sets.

**Q7 (mechanical).** The cached `.txt` renders the stacked `F⊩▶×μ` symbol inconsistently across pages
(e.g. `F⊩▶×μ` on p.160 vs `F-prime-strip`-style collapse elsewhere). Node names in `arrows.csv` are
transliterated so they stay greppable; if exact glyph fidelity matters, the PDF page (p.152 for the
diagram) is the authority. M1 read the extracted text only, per the task's static-only rule.
