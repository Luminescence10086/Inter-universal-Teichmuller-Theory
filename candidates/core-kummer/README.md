# Continuous Kummer comparison tools

Lean 4.34.0-rc2. From this directory: `lake build CoreKummer`.
Dependencies use the existing local Mathlib cache via path-only lake-manifest;
do not run `lake update` as part of a bounded replay.

The four ContinuousKummerTheory files are Apache-2.0 sources from
`https://github.com/lana-agents/continuous-kummer-theory`, commit
`98b67dfe9c82415aa17caa633d93960b6829af2e`, with four `haveI` to `have`
linter migrations. See LICENSE.upstream and
`research/core-kummer-2026-10-24/upstream-port.patch` from the repository root.

`ValuationSupport` compiles the neighboring
`core-local-global/KummerValuationSeparation.lean` without changing that
project's configuration. `KummerClassValuationBridge` consumes the genuine
Kummer kernel theorem. `CohomologyReflection` gives an explicitly conditional
injectivity criterion for the genuine continuous H1 map.

These are Qp/generic cohomological tools, not an instantiation of original IUT
tempered groups or a proof of Corollary 3.12/abc. Precise statements, source
audit, open obligations, build logs and editor evidence are recorded in
`research/core-kummer-2026-10-24/README.md`.

The next verified entry point is `Boundary/Frontier.lean`: general discrete
valuations, actual finite-place completions, finite normalization precision,
rational-point decomposition reflection and a concrete Laurent/power-series
germ consumer. See `research/core-boundary-2026-10-24/README.md` for exact
assumptions, replay instructions and editor evidence. The original Lake roots
remain unchanged; the new entry is compiled with `lake env lean` explicitly.
Do not import Frontier together with its source-section modules: they use the
same declaration names. This extension still does not reconstruct tempered Pi
or close the original IUT comparison.
