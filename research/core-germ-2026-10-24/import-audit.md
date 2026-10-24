# Theta germ minimal import audit

The source checkout is `reviews/core-round/external/tate-curves-theta` at commit
`d1fba94861c886b671f4137ab35e24b7474c9e00`. Its upstream `lean-toolchain` is Lean
4.32.0; the candidate project uses Lean 4.34.0-rc2, so the upstream checkout's build
artifacts were not treated as compatible evidence. The upstream license is Apache-2.0;
the corresponding `LICENSE` was copied to `candidates/core-kummer/TateCurvesTheta/LICENSE.upstream`.
File-level source and candidate hashes are recorded in `port-source.json`.

## Why this four-file subset suffices for the germ core

`ThetaGermCore.lean` is the upstream `Kummer/ThetaGerm.lean` prefix through its
`end TateParameter` at source line 233. It retains the definitions and lemmas needed to
build and evaluate the actual power-series germ, including `binomCoeff`,
`TateParameter.thetaGerm`, coefficient evaluation, summability/evaluation lemmas, and
`thetaGermUnit`. Its only source-import substitution is replacing
`TateCurvesTheta.Kummer.ThetaValues` with `TateCurvesTheta.Theta.Periodicity`; it also
closes the outer `TateCurvesTheta` namespace after the cut. This is a prefix extraction,
not a claim that the complete upstream `ThetaGerm` module has been ported.

The local import chain is deliberately narrow:

```text
QParameter/Basic.lean
  └─ Mathlib normed-field/log/limits imports
Theta/Basic.lean
  ├─ Mathlib ultrametric/infinite-sum/power imports
  └─ TateCurvesTheta.QParameter.Basic
Theta/Periodicity.lean
  ├─ Mathlib infinite-sum ring imports
  └─ TateCurvesTheta.Theta.Basic
Kummer/ThetaGermCore.lean
  ├─ ContinuousKummerTheory.Kummer.Decomposition
  ├─ Mathlib.RingTheory.Valuation.LocalSubring
  └─ TateCurvesTheta.Theta.Periodicity
```

`ThetaValues.lean` pulls in `ContinuousKummerTheory.Kummer.ZHat`, `Restriction`,
`Theta.Durfee`, `Theta.Inversion`, and `QParameter.BaseChange`. Those are not needed by
the extracted germ prefix: the point-evaluation/reduction and later ZHat-specific tail
begin after the cut, and the germ core gets `theta`, `thetaTerm`, and q-periodicity via
the three smaller theta files above. The later `Boundary.ThetaGermTransport` source
imports this germ core and the already-local `Boundary.ProjectiveComparison`; its local
theta dependency is therefore provided by these four files rather than the full
23-file upstream `TateCurvesTheta` import closure.

## Build evidence boundary

The parent agent reports that the four entries in `port-build-exits.json` were built
individually with exit code 0 and that their corresponding per-file logs are warning-free.
The recorded toolchain context is the candidate project's Lean 4.34.0-rc2. I did not run
Lean or those build commands; this paragraph reports the parent-provided build record only.
It does not establish that the full upstream `ThetaGerm` file or the larger
`ThetaGermTransport` source compiled successfully. The previously observed combined
transport build log is separate evidence and was not used as proof of the four-file
port's status.
