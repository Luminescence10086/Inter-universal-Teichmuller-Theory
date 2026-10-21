# Finite orbit hull tool

From this candidate project directory:

```powershell
python tool/hull_tool.py --input tool/examples/three-cycle.json --out tool/runs/my-cycle
python -m unittest discover -s tool -p test_hull_tool.py
```

The component emits **PROPOSED**, unverified results. Use the workspace's
`model-tools/run.py hull --input FILE --out DIR` shared entry point to run Lean
and its axiom audit; only that runner may return VERIFIED. A fresh output directory
is required. Component stdout contains one JSON object, including on rejection.
The four artifacts are request.json, result.json, certificate.lean, manifest.json.
Invalid inputs return exit 2 and INVALID_INPUT artifacts when the output directory
is writable and fresh. They are domain/resource errors, not mathematical counterexamples.

## Input contract

Strict JSON object, schema 1. Required fields: `schema`, `p`, `N`, `thresholds`,
`permutations`. The only optional field is boolean `require_enlargement`, default
true. Unknown/duplicate fields, non-integer numbers, boolean-as-integer values,
non-finite numbers, and invalid bijections are rejected.

Limits: 1 MiB input, 1 <= n = len(thresholds) <= 16, 1..128 permutations,
0 <= N <= 10000, 2 <= prime p <= 2147483647, and 0 <= each threshold <= N.
These are conservative computational limits; excluded inputs are not refutations.
Every permutation is an array of length n listing sigma[0],...,sigma[n-1], a
bijection of 0,...,n-1. Duplicate permutations are allowed; the finite family
forgets duplicates while witnesses retain the original input index. No group
closure or inverse closure is assumed.

The standard left action is `A_sigma(x)[j] = x[sigma_inverse[j]]`. It corresponds
exactly to the model's `permAct sigma.symm` image. Hence the output coordinate j
is `min_sigma thresholds[sigma_inverse[j]]`. The first minimum in input order
provides the witness permutation index and source coordinate. The three-cycle
example distinguishes this convention from forward reindexing.

When require_enlargement is true the finite family must contain identity. The
tool returns the nonnegative integer `sum(k[j] - hull[j])` and certifies the exact
relation `card(Box k) * p^e = card(Box hull)`. Without the identity this mode is
rejected conservatively. When false, enlargement/ratio exponents are null and
no enlargement claim is made, even if the particular input happens to contain id.

## Certificate and result contract

Result fields include hull_thresholds, per-coordinate witnesses, box_exponent,
hull_exponent, enlargement_exponent, cardinality, action, and domain. Cardinality
is kept exactly as powers of p; huge integers are never expanded. The domain
metadata are proposals until verification. The certificate embeds the same input
vectors, explicit permutations and inverse vectors, output vector, and witnesses.
Lean proves every permutation's two inverse laws, primality and boundedness,
the action bridge, each attained witness and all lower bounds, the exact returned
exponent sums, and equality of the returned threshold function with `hullThresh`.
It then applies the existing arbitrary-coordinate-product minimality theorem and
exact counting/budget theorems. Arbitrary supported new JSON requires no manual
proof edits. A Lean resource failure is a verification failure, never a counterexample.

Manifest schema 1 has component=hull, status=PROPOSED, absolute project/certificate,
prepare_target=Candidates.HullTool, theorem_names, request_sha256,
certificate_sha256, result, domain, limits. SHA256 covers the actual emitted
certificate bytes and the sorted/indented UTF-8 request JSON ending in LF.
There are no shell commands in manifests. Fixed theorem names live under
HullToolCertificate: input_valid, action_convention, witnesses_valid,
exponents_valid, thresholds_eq_hull, product_minimality, cardinality; plus
identity_mem and enlargement when requested. The shared runner prints their axioms.

The original OrbitQuotient file and its 2/3/4 theorem are unchanged. Examples
include that case, a non-involutive 3-cycle with p=3,N=4, a p=5,N=3 single-cycle
family without identity, and an invalid bijection. Tests independently enumerate
finite sets and their projections using forward coordinate assignment.

This is finite cardinality, not log volume, Haar/Arakelov measure, or an actual
IUT/Ind3 error budget. No receipt, pin, or fact-tree admission is created.
