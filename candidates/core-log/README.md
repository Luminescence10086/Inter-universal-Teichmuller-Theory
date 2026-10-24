# Pinned p-adic logarithm port and actual Q3 instance

Upstream: https://github.com/lana-agents/padic-log-volume.
Pinned upstream commit: 9a190da26368465ccf92561bc283fe710ae730f0.
Source: PadicLogVolume/PadicLog.lean; Apache-2.0 copyright header and LICENSE retained.
Lean: leanprover/lean4:v4.34.0-rc2.
Mathlib: 85e3a25e006c35636f0e53b0e9296caca2685bc0, reused as an absolute path dependency.

The full upstream theorem set is retained. Imports are narrowed from `Mathlib` to
specific modules. NatNorm/Series/Limit/Surjective assumptions are generalized from
a rank-one valued field with its induced norm to `[NormedField k] [IsUltrametricDist k]`.
Their proofs use only these norm properties. Uniform retains the original discrete
valuation assumptions. Unused section variables are explicitly omitted.

`CoreLog/QpThree.lean` uses Mathlib's standard norm, complete-space instance and
field on the actual type `ℚ_[3]`. It does not install a different norm via
`open scoped Valued`, and does not assume an unidentified norm comparison.
It proves convergence, multiplication compatibility, and the exact image equation
`padicLog '' {x : ℚ_[3] | ‖x - 1‖ < 1} = {y | ‖y‖ ≤ (3 : ℝ)⁻¹}`.

This is a local-field result. It does not establish the IUT cross-theater transport,
Corollary 3.12, the abc consequence, or admission into the project's fact tree.

Run from this directory:

```powershell
lake env lean PadicLogVolume/PadicLog.lean -o .lake/build/lib/lean/PadicLogVolume/PadicLog.olean
lake env lean CoreLog/QpThree.lean -o .lake/build/lib/lean/CoreLog/QpThree.olean
lake env lean CoreLog/Audit.lean
```

Evidence, source diff, and current status are under `../../reviews/core-round/log/`.
The initial full `import Mathlib` attempt was interrupted because of a loading
bottleneck; the narrowed full port is the version actually checked.

OPEN: a finite-sum truncation error theorem. The separately verified arithmetic
helper was copied to `CoreLog/PrecisionArithmetic.lean`, but has not yet been joined
to the analytic tail in this project. No claim of a verified numerical certificate
or truncation theorem is made.

