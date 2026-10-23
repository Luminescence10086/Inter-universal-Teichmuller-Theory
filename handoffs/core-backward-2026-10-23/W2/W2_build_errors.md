# W2 — verbatim error output of the failed elaborations

Kept for provenance: four elaborations of `candidates/core-transport/CollectionProvenance.lean` were
run in total. The accepted one is build 4 (exit 0, stderr 0 bytes, `W2_stdout.log` / `W2_stderr.log`).
Below is the error text of builds 1–3, copied from the command output. In all three cases the run
finished with exit code 1 and **stdout** carried the messages (Lean writes diagnostics to stdout), so
the captured stderr was empty even on failure — the acceptance criterion used throughout was
"exit 0 **and** no `error:` line", not the stderr byte count alone.

## Build 1

Two substantive problems:

1. the unused-variable linter rejects two structure field binders under `-DwarningAsError=true`;
2. two `calc` steps fail because `rw [CoreLog.norm_three]` rewrites `‖(3 : ℚ_[3])‖` but not the
   syntactically different `‖((3 : ℕ) : ℚ_[3])‖` that occurs in `PadicLogVolume.norm_logRem_le`'s
   conclusion (the two are defeq but not syntactically equal, so `rw` misses the second occurrence).

```
CollectionProvenance.lean:168:17: error: Variable name `v` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _v

Note: This linter can be disabled with `set_option linter.unusedVariables false`
CollectionProvenance.lean:172:17: error: Variable name `v` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _v

Note: This linter can be disabled with `set_option linter.unusedVariables false`
CollectionProvenance.lean:328:70: error: Type mismatch
  h
has type
  ‖PadicLogVolume.logRem 3‖ ≤ ‖↑3‖ * 3⁻¹
but is expected to have type
  ‖PadicLogVolume.logRem 3‖ ≤ 3⁻¹ * 3⁻¹
CollectionProvenance.lean:336:71: error: Type mismatch
  h
has type
  ‖PadicLogVolume.logRem (-3)‖ ≤ ‖↑3‖ * 3⁻¹
but is expected to have type
  ‖PadicLogVolume.logRem (-3)‖ ≤ 3⁻¹ * 3⁻¹
```

Consequence visible in build 1's `#print axioms` output: the five declarations downstream of the two
failed `calc` steps reported `sorryAx` in their dependency list. That was an *error* state, not a
silently accepted proof — the file never was presented as passing.

### Repair 1 (the only proof-level repair)

`norm_logRem_three_le` and `norm_logRem_neg_three_le` now bridge the two norm shapes explicitly:

```lean
  have h' : ‖PadicLogVolume.logRem (3 : ℚ_[3])‖ ≤ (3 : ℝ)⁻¹ * (3 : ℝ)⁻¹ := by
    simpa only [Nat.cast_ofNat, CoreLog.norm_three] using h
```

and analogously with `norm_neg` added for `-3`. Statements unchanged; no other proof needed repair.

## Build 2 — linter workaround, attempt A

```
CollectionProvenance.lean:161:82: error: unexpected token 'set_option'; expected 'lemma'
```

Cause: written as `set_option linter.unusedVariables false in` **between** the structure's docstring and
the `structure` command. A docstring must be followed immediately by the declaration it documents, and
Lean also rejects `set_option … in` in that position; the parser was still expecting a declaration after
the docstring.

## Build 3 — linter workaround, attempt B

```
CollectionProvenance.lean:161:82: error: unexpected token 'set_option'; expected 'lemma'
```

Cause: the same positioning mistake, with the `in` removed — a bare `set_option` command still cannot
sit between a docstring and its declaration.

### Repair 2 (mechanical, no proof changed)

The option command was moved **before** the structure's docstring, and
`set_option linter.unusedVariables true` restores the linter immediately after the structure. The
structure keeps exactly the binder shapes stated in the task, `∀ v, ℕ → ℚ_[3]` and `∀ v, ℚ_[3]`,
instead of being renamed to `∀ _v, …` to appease the linter.

## Build 4 — accepted

```
exit=0  stderr=0 bytes  stdout=6702 bytes (the 32 required #print axioms lines)
```

See `README.md` for the full per-declaration list, the file hash and the scope statement.
