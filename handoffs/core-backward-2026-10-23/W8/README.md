# W8 — M-i toy: divide-back **with the twist term explicit**

Date: 2026-10-23. Scope: **(M-i) of `research/core-backward-2026-10-23/h3-prerequisites.md`, toy
shape only.** Not a fact-tree node, not a registry entry, not evidence for or against any IUT claim.

## Deliverable

One new file, and nothing else in the candidate tree:

| item | value |
|---|---|
| file | `candidates/core-transport/DivideBackTwist.lean` (**did not exist** before this round — checked at start; it was created, not overwritten) |
| namespace | `DivideBackTwist` |
| lines / bytes | 354 / 20415 |
| sha256 | `DD685D61F0E15A1CCEBDDECFDBFBC66FC377B76EA2315349CBB2B346328532A8` |
| declarations | 21 (2 `def`s, 19 theorems), **each** followed by `#print axioms` at the file end |
| build | exit code **0**, stdout 2041 B, **stderr 0 B** |

## Commands

Built from `candidates/core-transport`:

```
lake env lean -DwarningAsError=true DivideBackTwist.lean
```

Raw logs in this directory (UTF-8, no BOM, captured with `cmd /c "... 1> ... 2> ..."` so byte counts
are real):

* `compile.stdout.log` — 2041 B, the 21 axiom lines and nothing else;
* `compile.stderr.log` — **0 B**.

No repair round was needed: the first compile under `-DwarningAsError=true` returned exit 0 with
empty stderr. (The unused-variable trap is avoided by using explicit binders throughout, no section
variables; the only `set_option`-class concern, unused hypotheses, does not arise.)

## Axioms

All 21 declarations print exactly:

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

Verbatim sample (identical for every entry, see `compile.stdout.log`):

```
'DivideBackTwist.twistReading' depends on axioms: [propext, Classical.choice, Quot.sound]
'DivideBackTwist.divideBack_twist' depends on axioms: [propext, Classical.choice, Quot.sound]
'DivideBackTwist.twist_insensitive_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Axiom set is contained in `{propext, Classical.choice, Quot.sound}`; in particular the two `def`s
print the same set (they inherit `Classical.choice` from the `tsum`-based library definitions they
mention), so nothing in the file is axiom-free-by-luck or axiom-carrying-by-accident.

Forbidden-substring scan on the file (word-boundary regex, docstrings included): `sorry` 0,
`admit` 0, `opaque` 0, `native_decide` 0, `axiom` 0. The only occurrence of the letters
`axiom` is the 21 required `#print axioms` lines (`axioms` does not match `\baxiom\b`).

## The three required statements (verbatim, with line numbers)

`DivideBackTwist.lean:156`

```lean
theorem twistReading (u x : ℚ_[3]) (hu : ‖u - 1‖ < 1) (hx : ‖x - 1‖ < 1) (M : ℕ) :
    CoreTransport.localLog ((u * x) ^ M) =
      (M : ℚ_[3]) * CoreTransport.localLog u + (M : ℚ_[3]) * CoreTransport.localLog x
```

`DivideBackTwist.lean:179`

```lean
theorem divideBack_twist (u x : ℚ_[3]) (hu : ‖u - 1‖ < 1) (hx : ‖x - 1‖ < 1) (M : ℕ)
    (hM : M ≠ 0) :
    CoreTransport.localLog ((u * x) ^ M) / (M : ℚ_[3]) =
      CoreTransport.localLog u + CoreTransport.localLog x
```

`DivideBackTwist.lean:205`

```lean
theorem twist_insensitive_iff (u : ℚ_[3]) (hu : ‖u - 1‖ < 1) (M : ℕ) (hM : M ≠ 0) :
    (∀ x : ℚ_[3], ‖x - 1‖ < 1 →
        CoreTransport.localLog ((u * x) ^ M) / (M : ℚ_[3]) = CoreTransport.localLog x) ↔
      CoreTransport.localLog u = 0
```

`‖u * x - 1‖ < 1` is supplied inside `twistReading` by
`PadicLogVolume.norm_mul_sub_one_lt hu hx`, as required; multiplicativity is
`PadicLogVolume.padicLog_mul`, the power law is `PadicLogVolume.padicLog_pow`, both read through
`localLog_eq_padicLog`.

## Anti-degeneracy: the term is exhibited, and one concrete reading is proved non-zero

* `divideBack_twist_four_one`, `divideBack_twist_four_one_sq`: the identity written out at `u = 4`,
  `x = 1`, `M = 2` —
  `localLog (4 ^ 2) / 2 = localLog 4 + localLog 1`. The twist's reading `localLog 4` appears as an
  addend on the right; it is not cancelled by the divide-back.
* **Non-vanishing was proved, not assumed**: `norm_localLog_four : ‖localLog 4‖ = 1/3`, hence
  `localLog_four_ne_zero : localLog 4 ≠ 0` and `twistResidue_four_ne_zero : twistResidue 4 ≠ 0`.

How. Split the series at its leading term (`Summable.tsum_eq_zero_add`):
`localLog 4 = (4 - 1) + tail`. The leading term is `3`, of norm `1/3`
(`CoreLog.norm_three`). For the tail, the `n`-th term (`n ≥ 1`) has norm
`‖3‖ ^ (n + 1) * ‖(n + 1 : ℚ_[3])‖⁻¹ = ‖3‖ ^ (n + 1 - v)` with `v = v_3(n + 1)`
(`PadicLogVolume.norm_natCast_eq_pow`, `PadicLogVolume.norm_logTerm`); `v < n` because
`3 ^ v ≤ n + 1 < 3 ^ n`, the strict inequality being `1 + 2 n ≤ 3 ^ n` (`one_add_mul_le_pow`)
together with `Nat.ordProj_le`. Hence `‖tail‖ ≤ ‖3‖ ^ 2 = 1/9 < 1/3`, and the ultrametric maximum
principle (`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`) gives `‖localLog 4‖ = 1/3`.

What this is **not**: no root-of-unity hypothesis and no statement about the kernel of the logarithm
is used, and the witness lives in `ℚ_[3]`; it does **not** exhibit a non-root-of-unity in the
source's fiber.

## Non-claims (stated in the module docstring as well)

1. Does not value the source's `M` (M-ii).
2. Does not construct the divide-back map on the tensor-power Frobenioids of
   (Ob4-1)/(Ob4-2)/(Ob4-3); `x ↦ x ^ M` is not `det^{⊗M}`, and `ℚ_[3]` is not the localisation of
   an arithmetic line bundle.
3. Says nothing about either normalization of (M-iii), nor about log-volumes, log-shells,
   prime-strips, Θ-links, `Ism`, Hodge theaters, Corollary 3.12, or any audited `external/iut`
   interface.
4. The `↔` of `twist_insensitive_iff` is a statement about this toy's reading; it is **not** a
   reading of (Ob4-3)'s *estimates* of log-volumes, which remain an estimate-level claim.
5. `localLog_four_ne_zero` is a numerical witness in `ℚ_[3]`, not a witness in the source's setting.

## Restatement note (why nothing was imported)

`candidates/core-transport/lakefile.lean` declares the single library `CoreTransport`, whose modules
are those under `CoreTransport/`. `DivideBackLaw.lean` (W3) and `ExecutionProvenance.lean` are
top-level modules of the package: not Lake targets, no `.olean`, therefore **not importable**. The
declarations needed from them are restated with the same statements —
`algorithmRun`, `algorithmRun_eq_partialSums`, `localLog_eq_padicLog`, `hasSum_logTerm_localLog`,
`localLog_pow_eq_smul` — and carry no new mathematics.

One deliberate, recorded difference: `localLog_pow_eq_smul` is stated **without** `M ≠ 0`, because
its upstream `PadicLogVolume.padicLog_pow` needs none (the identity holds at `M = 0`, both sides
`0`). The `M ≠ 0` is carried by `divideBack_twist`, where it is genuinely needed — for the division.

## What the toy adds to (M-i)

The source asserts the tensor-power twist has "no substantive effect". The toy replaces the
assertion by an equation with a visible term: the divide-back of the twisted `M`-th power is
`localLog u + localLog x`, where `localLog u` is the twist's own reading, and insensitivity to the
twist is **equivalent** to that term vanishing. That equivalence — not any estimate — is what a
source-level "no substantive effect" would have to be an instance of.
