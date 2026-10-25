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
lake build
lake env lean -DwarningAsError=true CoreLog/Precision.lean
lake env lean -DwarningAsError=true CoreLog/PrecisionQpThree.lean
lake env lean -DwarningAsError=true CoreLog/Audit.lean
```

This branch contains the verified sources and the replay commands above.
Historical evidence that is not tracked on this branch is described in the
parent research workspace; it is not required to reproduce these CLI checks.
The initial full `import Mathlib` attempt was interrupted because of a loading
bottleneck; the narrowed full port is the version actually checked.

`CoreLog/Precision.lean` joins the integer valuation helper to the analytic
logarithm tail. If `r ≥ 1`, `‖x - 1‖ ≤ ‖p‖ ^ r`, and `2 * M ≤ N`, then

```text
‖padicLog x - ∑ n in Finset.range N, logTerm x n‖ ≤ ‖p‖ ^ M.
```

`CoreLog/PrecisionQpThree.lean` specializes this to actual principal units of
`ℚ_[3]`: the `2 * M`-term truncation has error at most `(3 : ℝ)⁻¹ ^ M`.
All four new theorems have passed strict Lean CLI checking with
`-DwarningAsError=true`; their printed axioms are contained in `propext`,
`Classical.choice`, and `Quot.sound`. No `sorry` or new axiom is used.

This closes the former finite-sum truncation gap at CLI level. It is a uniform
analytic error bound, not an executable interval-arithmetic numerical
certificate. No new editor observation or fact-tree admission is claimed.

