# K4 — execution provenance (toy province) — delivery log

Task K4 of `handoffs/core-backward-plan-2026-10-23.md` (§二 K4 row, §三 doctrine).
Workspace `D:\Inter-universal Teichmüller Theory`. One new Lean file, no existing file touched.

## 1. Deliverable

`candidates/core-transport/ExecutionProvenance.lean` — namespace `ExecutionProvenance`.

* sha256 `f37a80d6de6872f5ed0a23d9f39c9557a79de8cc5cd05110c148c74d79c53543`
* 11579 bytes, 208 lines, 11 declarations
  (`algorithmRun`, `algorithmRun_eq_partialSums`, `localLog_eq_padicLog`,
  `hasSum_logTerm_localLog`, `LegalExecution`, `value_eq_localLog`, `value_unique`,
  `value_mem_logImage`, `logImage_Q3_eq_closedBall`, `norm_four_sub_one`, `witnessFour`)
* forbidden tokens: `sorry` 0, `admit` 0, `opaque` 0, `native_decide` 0, `axiom` keyword 0
  (only the `#print axioms` commands contain the string "axioms"). The scan was run twice: the
  first pass matched a bare `admit` inside the prose word "admitted" in a docstring, which was
  reworded to "allowed" so that a token scan cannot produce a false positive.

## 2. Exact commands and results

Working directory for both commands: `candidates/core-transport`.

```text
lake env lean -DwarningAsError=true ExecutionProvenance.lean
  -> exit code 0, stderr 0 bytes, stdout 1002 bytes, wall clock 28.6 s
```

Raw byte redirection was done with `cmd /c "... 1> lean_stdout.txt 2> lean_stderr.txt"`; the
PowerShell `>` operator writes UTF-16LE and was not used, so the two logs are the literal stdout /
stderr of the command above.

Independent checker output `check.json` in this directory was **not written by me** and was left
untouched. It records the same command (`argv` = `lake env lean ExecutionProvenance.lean`, without
the `-D` flag), `exit 0`, `errors 0`, `warnings 0`, `ok true`, `forbidden []`, and its
`stdout_sha256` / `stderr_sha256` are byte-identical to the two log files below:

* `lean_stdout.txt` sha256 `452babcca464b5fe20c33f2071cfb99f6166fb2b5559783a87049de411b152f0`
* `lean_stderr.txt` sha256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (empty)

## 3. Axioms, verbatim (10 lines of `lean_stdout.txt`)

```text
'ExecutionProvenance.algorithmRun' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExecutionProvenance.algorithmRun_eq_partialSums' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExecutionProvenance.localLog_eq_padicLog' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExecutionProvenance.hasSum_logTerm_localLog' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExecutionProvenance.value_eq_localLog' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExecutionProvenance.value_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExecutionProvenance.value_mem_logImage' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExecutionProvenance.logImage_Q3_eq_closedBall' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExecutionProvenance.norm_four_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExecutionProvenance.witnessFour' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every line is a subset of `{propext, Classical.choice, Quot.sound}`.

## 4. What each item of the task is discharged by

| required | declaration |
|---|---|
| `algorithmRun` partial sums of the same series, `Finset.range` | `algorithmRun`, with `algorithmRun_eq_partialSums` proving `algorithmRun x = fun n => ∑ k ∈ Finset.range n, PadicLogVolume.logTerm x k` by `rfl` |
| `structure LegalExecution` with the six fields | `LegalExecution`, field order and types exactly as specified, `converges : Filter.Tendsto steps Filter.atTop (𝓝 value)` |
| `value_eq_localLog` from `converges` + `steps_eq` + the library theorem | `value_eq_localLog` |
| `value_unique` | `value_unique` (`rw [value_eq_localLog e₁, value_eq_localLog e₂, h]`) |
| non-vacuity at input `4` | `norm_four_sub_one` (`‖(4:ℚ_[3]) - 1‖ = ‖3‖ = 1/3 < 1` via `CoreLog.norm_three_lt_one`), `def witnessFour`, and `example : LegalExecution := witnessFour` |
| value in the principal-unit log image | `value_mem_logImage`, `⟨e.input, e.mem, (value_eq_localLog e).symm⟩` |
| `#print axioms` for every theorem | last 10 commands of the file |

One extra theorem, `logImage_Q3_eq_closedBall`, states that `CoreTransport.logImage ℚ_[3]` is the
whole closed ball of radius `(3:ℝ)⁻¹`. It is there to make the K4 point sharp: the image condition
that the audited interfaces carry as a field (`EtaAlg.realisation`) is satisfied by an entire ball
of values, so it can never determine a value. It is the same statement as
`DelegatedLogBridge.logImage_Q3_eq_closedBall`, rederived here (see §6).

`value_mem_logImage` is derived, not assumed: it is *not* a field of `LegalExecution`. That is the
whole difference from the audited interfaces, where the analogous statement is a hypothesis.

## 5. Does `value_eq_localLog` really consume the convergence proof?

Yes, and there is no other route to its conclusion. The goal is `e.value = localLog e.input`, and
`e.value` is an opaque structure field: the only statement in the whole file that connects
`e.value` to anything is `e.converges`. The proof builds `Tendsto (fun n => ∑ k ∈ Finset.range n,
logTerm e.input k) atTop (𝓝 e.value)` with `hrun` (from `e.converges` after `rw [← e.steps_eq]`)
and `hsteps` (that statement rewritten by `algorithmRun_eq_partialSums`), builds the *same* limit
statement at `𝓝 (localLog e.input)` from `(hasSum_logTerm_localLog e.mem).tendsto_sum_nat`, and
closes with `tendsto_nhds_unique`. Deleting `hsteps` leaves the goal unprovable, and deleting
`e.converges` removes the only source of `𝓝 e.value`.

Mechanical check of the same claim (a probe file, deleted afterwards, so no failing proof is left
anywhere): a copy of the deliverable with `value := CoreTransport.localLog 4` replaced by
`value := (0 : ℚ_[3])` in `witnessFour` fails to compile, at the `converges` field:

```text
ExecutionProvenance.lean:189:4: error: Type mismatch
  HasSum.tendsto_sum_nat (hasSum_logTerm_localLog norm_four_sub_one)
has type
  Tendsto (fun n => ∑ i ∈ Finset.range n, PadicLogVolume.logTerm 4 i) atTop (𝓝 (CoreTransport.localLog 4))
but is expected to have type
  Tendsto (fun n => ∑ k ∈ Finset.range n, PadicLogVolume.logTerm 4 k) atTop (𝓝 0)
```

i.e. the value cannot be chosen: with the trace pinned to `algorithmRun` by `steps_eq`, the
convergence field can only be discharged at the algorithm's actual limit. This is what the type
discipline buys; `value_unique` states it for two executions at the same input.

## 6. One structural finding: `DelegatedLogBridge` is not in the library target

`DelegatedLogBridge.lean` is a top-level module of the package, but `lakefile.lean` only declares
`lean_lib CoreTransport`, and no `DelegatedLogBridge.olean` exists in
`.lake/build/lib/lean`. Two consequences, both measured, not assumed:

```text
lake build DelegatedLogBridge
  -> error: unknown target `DelegatedLogBridge`      (exit 1)
lake env lean <file importing DelegatedLogBridge>
  -> error: unknown module prefix 'DelegatedLogBridge'   (exit 1)
```

So this file imports `CoreTransport.Basic` + `CoreLog.QpThree` instead, and restates the two
definition-level facts it needs: `localLog_eq_padicLog` (`unfold …; rfl`, identical to
`DelegatedLogBridge.localLog_eq_padicLog`) and `hasSum_logTerm_localLog` (from
`CoreLog.principal_unit_log_hasSum`, identical to `DelegatedLogBridge.hasSum_logTerm_localLog`).
Both are recorded in their docstrings as definition-level wiring, not new mathematics. No olean was
fabricated for `DelegatedLogBridge` and no existing file was edited; the package's source directory
still contains exactly the same files plus this one.

Docstring form: Lean's module docstring syntax is `/-! … -/`; `/-- … -/` attaches to a declaration.
The required caveat (toy province, partial-sum algorithm of the p-adic logarithm on `ℚ_[3]`, not the
η-algorithm of IUT, nothing about Θ-link / `Ism` / Cor 3.12, type discipline rather than new
mathematics) is in the module docstring, and is repeated in the `/-- … -/` docstring of
`algorithmRun`.

## 7. What this toy province does not establish

* It does **not** implement the η-algorithm of IUT, and it is not a step toward doing so.
* It constructs no Θ-link, no `Ism`, no Corollary 3.12, no Galois action, no adelic or hull
  condition, no localisation, and no degree comparison.
* It does **not** show that any of the 11 audited interfaces can be recast in provenance form; it
  only shows that such a type can be written on one concrete example and that it determines its
  value there.
* `value_unique` says the value is a function of the input. That is uniqueness, not existence of a
  canonical construction for the IUT outputs, and it says nothing about whether the IUT η-algorithm
  is a function at all.
* Nothing here is evidence for or against any IUT claim, and no fact-tree / registry entry is
  touched.

No `GAP.md` is delivered: nothing failed. The file compiled on its first attempt (exit 0, no
repair rounds), so there is no failing goal to report.
