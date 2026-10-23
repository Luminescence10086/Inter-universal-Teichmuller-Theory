# W6 — gate record

Deliverable: `candidates/core-transport/ReadingFactorization.lean`
sha256 `6a756a88d57eed9892e749eb0c8abea75c1aa289bd0556f44c3e9f8e5fb2716d`, 881 lines,
83 declarations, 83/83 axiom reports.

## What it formalises

W4 showed the reading is *constant on a compatible chain*. W6 shows it **descends to the quotient**:

- `SameObjectStep c a b` = the recorded transition really transports the presentation; `SameObject` is its
  `ReflTransGen` closure (the closure is needed: no field relates `unit a b` to `unit b a`; on a compatible
  chain it is redundant, `sameObjectStep_direct`).
- `descendedReading := Quotient.lift (reading c) sameObject_reading_eq`, with the lift obligation proved
  per step (`reading_eq_of_transport`), plus `descendedReading_unique`.
- `descendedReading_mk : descendedReading c hc (Quotient.mk _ i) = c.reading i`.

## Gates

- CLI: exit 0, stderr 0 bytes; independent strict re-check **PASS** — 83 declarations, 0 errors,
  0 warnings, 83 axiom reports, axioms only `{propext, Classical.choice, Quot.sound}`.
- Editor: **0 errors, 0 warnings**; capture in `editor/vscode-observation-tree-2.txt`.
- Infoview: not attempted.

## Anti-degeneracy

On `chainBroken` (units `0->1 = 4`, `1->2 = 4`, `0->2 = 64`): `4*64 = 256 != 64` kills the one-step `0~2`
edge, yet `16*4 = 64` keeps `i1 ~ i2` while the readings are `localLog 4` and `0`. Hence **no
factorization through the quotient at all** (`no_factorization_on_broken`). The compatible twin has one
edge, all readings equal, `descendedReading` constant.

The builder states the honest limitation in the docstring: `step_input` is a field, so `SameObject` is
total and the quotient is a subsingleton on every chain; the weight rests on constancy.

## Why quotient rather than constancy

Constancy compares values along one chain; `Quotient.lift` produces the unique function *on the
isomorphism classes* — the object-level statement — and its failure becomes "no factorization through the
quotient", which is exactly the orbit-shaped obligation of `h1-coricity.md`. Nothing here touches IUT's
localization data, log-volumes, Θ-links or Cor 3.12. Core GAP stays OPEN.
