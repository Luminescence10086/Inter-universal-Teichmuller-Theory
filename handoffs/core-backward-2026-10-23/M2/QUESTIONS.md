# M2 — QUESTIONS

Ten items, ordered so that the tensor-power bookkeeping comes first. Each says where the source is
silent, not what the answer is. No factor below is computed by this task.

## Dividing back the tensor power (highest priority)

**Q1. Where is the map from the M-th-power reading to the original reading?**
(Ob4), p.133 / txt 8135–8144, rules out an "indeterminacy arising from confusion between a given
arithmetic line bundle and its M-th tensor power" *by assertion*. (Ob4-1)/(Ob4-2) then say the
non-tensor-power Frobenioids are recovered from the tensor-power ones only **up to twists** (monoids
not divisible at v∈V_non). So to read off a value for the original q-pilot one needs: (a) a definite M,
(b) the same M on both sides of the comparison, and (c) a reason the twist is invisible after
dividing by M. (c) is exactly (Ob4-3). Nothing in the audited units constructs (a), (b) or (c).

**Q2. Is the log-volume reading invariant under the tensor-power twist?**
(Ob4-3), p.134 / txt 8185–8189: "such tensor-power-twist indeterminacies will not have any substantive
eﬀect on our computations [i.e., of log-volumes]". This is the load-bearing sentence for the whole
division. Either μlog is invariant under the twist, or the twist contributes exactly 0 — the source
says neither, and gives no bound. A proof obligation, not a fact.

**Q3. Is M the same object in (Ob3-2), (Ob4) and (Ob4-1)?**
(Ob3-2) pins M only by the property "maps [...] an arithmetic line bundle to the M-th tensor power",
with a bare "cf." to N_E of Remark 3.1.1, (iv). (xi-d) then says "[a suitable positive tensor power of]
the determinant" again, without repeating the identification. One must prove the M of the hull
determinant, the M of the q-pilot side, and the degree-M of the naive Frobenius functor are one M.

**Q4. Does the determinant commute with the local→global localization, and with the log-volume?**
(cQ3) gives local objects at each v plus localization isomorphisms (⊼lc-gl_3), txt 8592–8601;
(xi-d) reads "localizations of arithmetic vector bundles"; Proposition 3.9, (iii) gets the global
log-volume by *adding* local ones (all but finitely many zero). Nowhere is it stated that
det^{⊗M}(localization) = localization(det^{⊗M}) or that the two additions agree.

## Factors left unnamed in the units that use them

**Q5. What is "the [suitably normalized, with respect to j∈|Fl|] log-volume" (xi-d, p.183 / txt 11022)?**
Two regions are read with it — 1,◦U and the q-pilot region on 1,◦U_Q. If the j-dependence does not
cancel identically, the claimed equality is off by a j-factor. Step (x), p.181 / txt 10904–10907,
uses the *average over j∈F_l^⋇*; (xi-d) does not say it is that average. Must be pinned or shown cancelling.

**Q6. What is the "suitable normalization" in Proposition 3.9, (iii), p.117 / txt 7089?**
This is the only place the global degree ↔ log-volume identification is made, and the normalization is
named but never written. (Ob3-3) repeats it as "by working with suitable normalization factors".
Any global factor must either be exhibited here or proved to cancel against the local weights of
Remark 3.1.1, (ii). At present it is an open slot.

**Q7. Does the vertical shift contribute a factor or only an iterate count?**
(xi-d), txt 11038–11047, applies the 1-column log-Kummer correspondence "in order to rectify the
vertical shift/mismatch". (Ob8), txt 8398–8403, says the comparable objects are subject to "arbitrary
iterates of the log-link". Proposition 3.9, (iv), (b) says log-volumes indexed by (n,m) are
*compatible* with those indexed by (n,m−1) — compatibility, not an equality of real numbers. Whether
the iterate count drops out of the scalar reading has to be proved.

## Where an inequality could become an equality

**Q8. Where is the step from (Ind3) "inequality [from above]" to the "precise equalities" of Remark 3.12.2(v)?**
Step (x), p.181 / txt 10910–10912, is explicit that the procession-normalized mono-analytic log-volumes
"convert the indeterminacy (Ind3) into an inequality [from above]". Remark 3.12.2(v), txt 11644–11653,
claims the 1-column gives "precise equalities [i.e., not just inequalities!]". No display in Remark
3.12.2 states between which two written quantities the equality holds, and no bridge between the
0-column inequality and the 1-column equality is given. This is the single most fragile point for K3.

**Q9. Can the hull enlargement change the reading?**
(xi-c)/(xi-d) read the log-volume "by slightly enlarging [...] by working with the holomorphic hull".
(Ob6), p.135 / txt 8228–8230, warns μlog(H_Φ(P)) "may be > μlog(P) and indeed = μlog(φ(P))". Also
Remark 3.12.2(v), txt 11624–11636, uses the hull to *absorb* the O×-indeterminacy without claiming
μlog is unchanged. So either the reading is taken on a hull whose log-volume is already known, or one
must prove the enlargement is μlog-null here.

**Q10. Is the choice of log-conjugate ring structure invisible to the reading?**
Remark 3.12.2(v), txt 11636–11644: the indeterminacy in choosing a composite of arrows in the
log-Kummer correspondence is "absorbed by passing to log-volumes", via log-link compatibility. But
"absorbed" is asserted for the *indeterminacy*, not proved for the *value*: no statement that two
different log-conjugates give the same real number. Needed before any single reading can be named.
