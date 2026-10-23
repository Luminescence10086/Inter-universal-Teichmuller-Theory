# M3 QUESTIONS — interpretive items handed back to the main line

No Lean was run. Each item is a place where a criterion choice or a reading would change a flag or a
delta claim. Items stay questions: nothing here is asserted in `interfaces.json` beyond the recorded
source facts.

1. **F1 and q-powers.** I marked `LGPLattice.native_q_marking = true` because `kum_gen`
   (Thm311LGP.lean:97-98) names `gaussGen`, whose body is `EtaleTheta.lgpValue` and whose docstring
   (Gauss.lean:260-261) calls the values `q_v^{j²}`. This is a q-power generator, not `D.qPilot` and not
   `D.qroot`. Is a q-power generator a "native q marking" for K1/K4, or should the flag be reserved for
   `D.qPilot.absLogQ`-type terms (in which case only `ThetaShift` is true)?

2. **F4 and equality.** `EtaAlg.ThetaShift` (MultiContainer.lean:105-107) is an equality of log-volumes,
   not an inequality. I recorded it as `true` with `kind: "equality"`. Does K5's "degree comparison" want
   only inequalities (in which case F4 is false for all 11 and every inequality is a separate theorem)?

3. **`Choice` targets the Θ-pilot, not the q-pilot.** `Choice` (EtaAlg.lean:141) = `BPS.Iso B (A.thetaBPS h)`,
   with `thetaBPS = ⟨A.etUnit h, D.thetaValD⟩` (138). The q-pilot enters only where `Wall` instantiates
   `B := A.qBPS h₂` (174-175). Is the intended reading that "the Step-1 choice is q-free", or is the
   q-pilot version simply not the interface's business? M3 records the fact, not the reading.

4. **`LatticeKummer`'s `L` is phantom.** Neither field mentions `L` (Kummer.lean:250,252), though the
   docstring (246-247) says "at every vertex of a log-theta-lattice". Is the intended content that
   `kum (n,m)` should be tied to `L.H (n,m)`'s container? The source does not say; M3 did not supply it.

5. **`EtaAlg.Side` vs `LogThetaLattice.H`.** Two opaque families of Hodge theaters exist
   (EtaAlg.lean:100 and Lattice.lean:92) and no declaration identifies them. Is a bridge intended in K1,
   or are they deliberately separate?

6. **`out` for a generic `B`.** The field is defined for every `B : BPS model D.bpsDegrees.bad`. Does the
   main line want a q-pilot-indexed version of `out` (so that "the output of the q-pilot input" is a
   first-class object), or is instantiation at use sites enough?

7. **`etUnitOnly` is unused.** The module docstring (EtaAlg.lean:45) says nothing below uses it except the
   checks, and it forces q/value-group blindness on any `EtaAlg`. Should K4's realisation requirement be
   stated for an `EtaAlg` at all, given this field?

8. **Scope of the name `ThetaShift`.** It does not live in `MultiContainer`; it is
   `Iut.Wall.EtaAlg.ThetaShift` (a name extension from MultiContainer.lean:105). Any future citation
   should use the full name. Same class of issue as T2's `restriction_kummer_thetaUnit` correction.

9. **Where else could these names live?** Within the pinned `reviews/core-round/external/*` set no other
   repository mentions `ThetaShift`, `LGPLattice`, `LatticeKummer`, `InHullOfImage` or `IsAdelic`
   (checked by name scan). Repositories outside the four pinned ones were not read; if the main line
   wants a cross-repository alias table, that is a separate task.
