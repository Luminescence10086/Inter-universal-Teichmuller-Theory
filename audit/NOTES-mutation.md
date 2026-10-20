# Mutation testing of the verification gates

**Analogy.** Mutation testing (PIT) does not ask whether a suite looks thorough; it
injects one fault at a time and asks whether a test kills it, and fault injection does
the same to a running system. Here the "tests" are the gates: one semantic mutation
per row, applied to a copy, and the gate that claims that defect must fire. The
repository's own comparators run; the gate logic is not re-implemented.

**What is exercised.** M1/M2/M4/M6 drive the real `tools/statement_lock.py` and
`tools/semantic_lock.py` `main()`; only their Lean-side seams (`project_constants`,
`validate_project`, `definition_bodies`) are substituted in memory, because re-running
`lake` is forbidden here and would rewrite tracked evidence. M3 runs
`verify_integrated.validate_catalog`/`audit_hypotheses`, M4 also
`bridge.require_theorem`, M5 `bridge.vendored_matches`, M7
`freshness.validate_project` on a copied `main` project; the `clean_checkout` column is
`bridges/check_clean_checkout.py`, run read-only as an unmutated probe.

**Strength gained: the gates are exercised, not assumed.** Eight mutations x seven
gates, three outcomes per cell. Every gate that makes a claim fired on the mutation
that makes it true (M1-M7); the innocuous control (M8: appended comment, reordered
JSON keys) did *not* reach the statement ledgers even though the byte gate did fire;
and unmutated copies pass every gate, so a wall of green is not "anything changed =
fail". Blindness is reported per cell instead of hidden: a statement rewrite with a
refreshed export is invisible to the byte gate, and a vendored body flip with an
identical elaborated type is invisible to the statement ledger. That is the division
of labour the stack claims, measured.

**Honest limits.**
- A mutation the gates cannot catch is not thereby a real defect; nor does a caught
  mutation certify a gate's judgement, since normalised elaborated text is only a
  conservative change proxy (the ledgers say so themselves). This tests the gates,
  not the mathematics: nothing here transports a proof or makes a theorem truer.
- `clean_checkout` is never mutated: injecting a blob needs a git object write
  (forbidden) and a temp copy has no `HEAD`; its comparator still runs read-only
  (16/16 main, 15/15 local, 36/36 bridge inputs byte-exact at HEAD).
- Statement mutations live in the *exported* statements plus a refreshed export (what
  a source edit plus a verifier re-run leaves); elaboration itself is not run.
- M6 deletes the theorem from the exported constants; unpinning a ledger *file* entry
  reads as an addition and passes (both ledgers' declared behaviour, kept as the
  `unpin_entry` probe, not counted as a defect).
