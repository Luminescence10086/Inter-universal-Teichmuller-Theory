# Verification nodes for Lean candidates (`cdsa/checks/`)

Two programs, both designed around one rule from this repository's review doctrine: **an
author's self-report is never the evidence for its own claim**. They are used as CDS-A
`command` executors, so their exit status is the gate and their JSON output is the artifact
a downstream edge hashes.

## `check_lean_candidate.py`

Re-runs the toolchain itself and derives every verdict from the compiler's bytes.

| assertion | where it comes from |
| --- | --- |
| zero error diagnostics | parsed from `lean` output, not from prose |
| zero warning diagnostics | same (strict mode; a warning is still an unexplained fact) |
| forbidden terms absent | `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `sorryAx`, comments stripped line-wise |
| axioms within whitelist | parsed from `#print axioms`, compared with `{propext, Classical.choice, Quot.sound}` |
| every theorem has an axiom report | declaration list from the source vs reported names (`--require-all-axioms`) |
| declarations exist | regex enumeration of `theorem`/`lemma`/`instance`/`def` |

Options: `--axiom-source` (the repo's `Candidates/Axioms.lean` convention), `--build-lib`
(the companion probe imports the module, so `lake build` must run first — otherwise the probe
dies with `unknown module prefix`, which is exactly what happened on the first attempt),
`--require-all-axioms`, `--json-out`.

Axiom names in the report are fully qualified (`Candidates.X.foo`) while the source enumerates
them unqualified; matching is on the last dotted component. Getting this wrong made the strict
mode report all 35 declarations of the existing pilot candidate as "unreported" — the first
version did exactly that.

## `claim_consistency.py`

Adversarial comparison of three artifacts produced separately: the README (what the author
says), the `.lean` source (what exists), and the checker JSON (what the compiler said).

1. exactly one `VERDICT:` line, from an allowed vocabulary;
2. no declaration is hidden from the README;
3. a proof-bearing verdict requires a passing checker artifact;
4. a failing artifact forbids a proof-bearing verdict (the overclaim detector);
5. naming `Cor 3.12`, the Θ-link, `Ism` or `abc` requires a hedging token within 400 chars;
6. the README must state the `lake env lean` reproduction command and the toolchain.

## `crosscheck_candidates.py`

The second-pass node: re-runs `check_lean_candidate.py` in **strict** mode in a fresh process
for each candidate, then `claim_consistency.py`, then scans both sources for the repository's
one forbidden identification — describing `A(k)` / `Q_p`-linear automorphisms as elements of
`Ism` (finding **F-01**, the most dangerous false bridge). That last check is prose-level, so
no compiler can ever catch it.

## Defects this tool had, found by pointing it at real candidates

Recorded because the audit is about not trusting self-reports — including this tool's own.

1. **Wrapped axiom lists were silently dropped.** `#print axioms` wraps a long axiom list onto
   a second line; a single-line pattern therefore dropped exactly the declarations with many
   axioms. On the rank-0 candidate this made 2 of 9 audited theorems look unreported, and the
   strict gate failed on a candidate that was in fact complete. Fixed by matching the closing
   `]` across newlines.
2. **Qualified vs unqualified names.** The report is fully qualified (`Candidates.X.foo`) while
   the source enumerates `foo`; matching them directly marked all 35 declarations of the
   existing pilot candidate as unreported.
3. **The companion probe needs a build.** `Candidates/Axioms.lean` *imports* the module, so it
   dies with `unknown module prefix 'Candidates'` unless `lake build Candidates` ran first —
   hence `--build-lib`.
4. **The hedge window was phrase-based and case-sensitive.** `Nothing here constructs … an Ism`
   was read as an unhedged claim, and later a leading `**no**` Cor 3.12 was also missed. The
   check now looks for a *negation token near the mention* (`no|not|none|nothing|never|without|
   absent|forbidden`) inside a 160-character window — the actual grammar of hedging — instead of
   a fixed phrase list inside 400 characters, which was simultaneously too loose (any distant
   hedge passed) and too strict (the commonest form failed).
5. **`VERDICT:` wrapped in backticks was invisible.** The rank-1 candidate wrote it as
   `` `VERDICT: CORE_PROVED` `` and the audit reported "found 0". The regex now tolerates
   markdown wrappers and a preceding heading marker.
6. **`candidates/orbit-quotient/lakefile.lean` does not exist on this branch.** The worker brief
   pointed at it; the only real pattern here is `candidates/pilot-shadow/lakefile.toml`. The
   brief was wrong, not the tool.

## Calibration (both directions, actually executed)

| control | command | result |
| --- | --- | --- |
| positive, existing candidate | `--project candidates/pilot-shadow --source Candidates/PilotShadow.lean --axiom-source Candidates/Axioms.lean --build-lib Candidates` | **PASS** — 35 declarations, 0 diagnostics, 10 audited theorems all on `{propext, Classical.choice, Quot.sound}` |
| negative, planted `sorry` | a one-line `theorem bad_sum : (1 : Nat) = 2 := by sorry` | **FAIL** — `lean exited 1`, 1 error, 1 warning, forbidden term at line 3, no axiom report |
| strict mode on the same candidate | `--require-all-axioms` | **FAIL** — 22 helper theorems carry no axiom report. This is a real observation about existing practice, not a tool defect: an unused-but-`sorry` helper would be invisible to a "main results only" audit |

`PASS` from any of these means **process integrity**. It is not mathematical admission, and it
says nothing about IUT, the Θ-link, `Ism` or Cor 3.12 — none of which is constructed here.
