# Finite-profile ledger certificate emitter

Run from `candidates/restricted-ledger`:

```powershell
python tool/ledger_tool.py --input tool/examples/restricted-preserves.json --out tool/runs/example
lake build Candidates.LedgerTool
lake env lean tool/runs/example/certificate.lean
python tool/test_ledger_tool.py
```

The emitter uses only the Python standard library. Its stdout is one JSON object.
Successful emission exits 0 with `PROPOSED`; this does **not** mean verified.
The shared replay runner is responsible for `VERIFIED` or
`VERIFIED_COUNTEREXAMPLE`, and for recording actual Lean exit status and axiom
dependencies. Missing/unsupported domain certificates exit 2 as `INSUFFICIENT`.
Malformed numeric or dimensional input exits 2 as `INVALID_INPUT`.

Input schema 1 contains a prime integer `p`, nonempty integer array `weights`, a
zero-based permutation array, and integer `scalar_valuations` of the same length.
Booleans are not integers. `domain.kind` must be `finite_profiles`, with a nonempty
array `profiles` of integer arrays and optional `base_index` (default 0).
Empty profiles and zero-dimensional tuples are not supported by this interface.
Duplicates and negative valuations are allowed.

The domain is **all actual Q_p tuples with every coordinate nonzero and with
valuation vector equal to one of the supplied profiles**, not merely the listed
power tuples. Scalars are the actual elements `a_j = p^(scalar_valuations_j)`.
No claim is made that this domain is a real IUT allowed domain.

For the action `relabel σ (slotwise a x)`, the profile at target coordinate `j`
is `e[σ⁻¹(j)] + s[σ⁻¹(j)]`. The ledger change is
`sum_j (w[σ(j)] - w[j]) e[j] + sum_j w[σ(j)] s[j]`.
Ledger preservation and `T Ω ⊆ Ω` are computed and proved independently.
A failed ledger check includes an actual witness `x_j = p^e_j`; Lean proves
membership in the domain and inequality of its two ledgers. Failure of domain
closure has its own actual power-tuple witness and theorem.

The automatic integer column Euclidean algorithm tracks unimodular changes
`V` and their inverses while reducing the difference matrix `A` to `[B,0]`.
It supplies at most `n` generators. In the JSON, generator vectors are rows,
`hgen_coefficients[k][i]` expresses profile difference `k` in these generators,
and `hmem_coefficients[i][k]` expresses generator `i` in actual differences.
The Lean certificate checks both inclusions directly and applies the existing
`restricted_ledger_combination_criterion`. Algorithm correctness, a canonical
normal form, linear independence, and minimality are **not** assumed or claimed
by the certificate. In particular `{0,2,3}` produces generator `1 = 3 - 2`,
which need not be an actual difference. Rank-zero certificates use `Fin 0`.

Each output directory contains `request.json`, `result.json`, `certificate.lean`,
and `manifest.json`. Invalid/insufficient outputs contain only a comment in the
certificate file and no theorem names. Reusing an output directory replaces its
certification material; callers must not treat an older success as current.
The manifest has no shell commands: it supplies a fixed helper build target,
absolute project/certificate paths, named conclusions, results and SHA-256
digests. All mathematical declarations are printed with `#print axioms`.
The helper and generated sources use no extra axioms or unchecked decision
procedure. Arithmetic uses kernel reduction through `decide`.

The emitter performs exact integer arithmetic and trial division primality
testing. Large inputs can be slow or produce large certificates; the replay
runner's timeout and Lean resource limits remain authoritative. Results are not
verified when replay fails or times out.
