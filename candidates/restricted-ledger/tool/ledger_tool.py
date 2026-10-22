#!/usr/bin/env python3
"""Emit untrusted finite-profile ledger calculations and kernel-checkable Lean.

Standard library only. Successful emission means PROPOSED, never VERIFIED.
Actual verification is performed by the shared, fixed-command replay runner.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import math
from pathlib import Path
import sys


class InputError(ValueError):
    pass


class Insufficient(ValueError):
    pass


def integer(value, name):
    if type(value) is not int:
        raise InputError(f"{name} must be a JSON integer (not boolean)")
    return value


def vector(value, name, size=None):
    if not isinstance(value, list):
        raise InputError(f"{name} must be an integer array")
    if size is not None and len(value) != size:
        raise InputError(f"{name} must have length {size}")
    return [integer(x, f"{name}[{i}]") for i, x in enumerate(value)]


def validate(raw):
    if not isinstance(raw, dict):
        raise InputError("request must be an object")
    if integer(raw.get("schema"), "schema") != 1:
        raise InputError("only schema 1 is supported")
    p = integer(raw.get("p"), "p")
    if p < 2 or any(p % q == 0 for q in range(2, math.isqrt(p) + 1)):
        raise InputError("p must be prime")
    w = vector(raw.get("weights"), "weights")
    n = len(w)
    if n == 0:
        raise InputError("weights must contain at least one slot")
    perm = vector(raw.get("permutation"), "permutation", n)
    if sorted(perm) != list(range(n)):
        raise InputError("permutation must be a bijection of zero-based slot indices")
    s = vector(raw.get("scalar_valuations"), "scalar_valuations", n)
    domain = raw.get("domain")
    if domain is None:
        raise Insufficient("an explicit finite_profiles domain certificate is required")
    if not isinstance(domain, dict):
        raise InputError("domain must be an object")
    if domain.get("kind") != "finite_profiles":
        raise Insufficient("unsupported domain kind; no admissible-domain conclusion available")
    profiles = domain.get("profiles")
    if not isinstance(profiles, list) or not profiles:
        raise InputError("finite_profiles requires a nonempty profile list")
    profiles = [vector(e, f"profiles[{k}]", n) for k, e in enumerate(profiles)]
    base = integer(domain.get("base_index", 0), "base_index")
    if not 0 <= base < len(profiles):
        raise InputError("base_index is outside the profile list")
    return {"schema": 1, "p": p, "weights": w, "permutation": perm,
            "scalar_valuations": s, "domain": {"kind": "finite_profiles",
            "profiles": profiles, "base_index": base}}


def integer_generators(profiles, base):
    """Column Euclidean elimination: A V = [B,0], track V and V^-1.

    B is an integer generating family with at most n columns. Neither the
    algorithm nor linear independence/minimality is part of the trusted proof.
    Lean verifies A=B G and B=A M directly, even if this code is defective.
    """
    m, n = len(profiles), len(profiles[0])
    a = [[profiles[k][j] - profiles[base][j] for k in range(m)] for j in range(n)]
    v = [[int(i == j) for j in range(m)] for i in range(m)]
    inv = [row[:] for row in v]

    def swap(i, j):
        for matrix in (a, v):
            for row in matrix:
                row[i], row[j] = row[j], row[i]
        inv[i], inv[j] = inv[j], inv[i]

    def add(target, source, q):
        for matrix in (a, v):
            for row in matrix:
                row[target] += q * row[source]
        inv[source] = [x - q * y for x, y in zip(inv[source], inv[target])]

    rank = 0
    for row in range(n):
        pivot = next((k for k in range(rank, m) if a[row][k]), None)
        if pivot is None:
            continue
        swap(rank, pivot)
        for k in range(rank + 1, m):
            while a[row][k]:
                q = a[row][rank] // a[row][k]
                add(rank, k, -q)
                swap(rank, k)
        if a[row][rank] < 0:
            for matrix in (a, v):
                for line in matrix:
                    line[rank] = -line[rank]
            inv[rank] = [-x for x in inv[rank]]
        rank += 1
        if rank == m:
            break
    b = [[a[j][i] for j in range(n)] for i in range(rank)]
    g = [[inv[i][k] for i in range(rank)] for k in range(m)]
    membership = [[v[k][i] for k in range(m)] for i in range(rank)]
    # Defensive checks, not the certification boundary.
    for k in range(m):
        for j in range(n):
            assert profiles[k][j] - profiles[base][j] == sum(g[k][i] * b[i][j] for i in range(rank))
    for i in range(rank):
        for j in range(n):
            assert b[i][j] == sum(membership[i][k] * (profiles[k][j] - profiles[base][j]) for k in range(m))
    return b, g, membership, v, inv


def calculate(req):
    w, s, perm = (req[k] for k in ("weights", "scalar_valuations", "permutation"))
    profiles, base = req["domain"]["profiles"], req["domain"]["base_index"]
    n = len(w)
    inverse = [perm.index(j) for j in range(n)]
    d = [w[perm[j]] - w[j] for j in range(n)]
    budget = sum(w[perm[j]] * s[j] for j in range(n))
    shifts = [sum(d[j] * e[j] for j in range(n)) + budget for e in profiles]
    images = [[e[inverse[j]] + s[inverse[j]] for j in range(n)] for e in profiles]
    b, g, mem, _, _ = integer_generators(profiles, base)
    bad = next((k for k, shift in enumerate(shifts) if shift), None)
    outside = next((k for k, image in enumerate(images) if image not in profiles), None)
    witness = None
    if bad is not None:
        e = profiles[bad]
        before = sum(w[j] * e[j] for j in range(n))
        witness = {"profile_index": bad, "profile": e,
                   "coordinates": [f"{req['p']}^({x})" for x in e],
                   "ledger_before": before, "ledger_after": before + shifts[bad],
                   "ledger_shift": shifts[bad]}
    return {"ledger_preserved": bad is None, "domain_invariant": outside is None,
            "d": d, "scalar_budget": budget, "base_equation": shifts[base],
            "profile_shifts": shifts, "image_profiles": images,
            "generators": b, "generator_count": len(b),
            "generator_values": [sum(x*y for x,y in zip(d, row)) for row in b],
            "hgen_coefficients": g, "hmem_coefficients": mem,
            "generator_method": "integer_column_euclid",
            "generator_claim": "two integer span inclusions; no minimality claim",
            "witness": witness, "domain_witness": None if outside is None else {
                "profile_index": outside, "profile": profiles[outside], "image_profile": images[outside]},
            "scope": "all nonzero actual Q_p tuples with one of the supplied profiles; not a real IUT admissibility certificate"}


def lean_vector(xs):
    return "![" + ", ".join(lean_vector(x) if isinstance(x, list) else str(x) for x in xs) + "]"


def certificate(req, result):
    p = req["p"]
    n, m, r = len(req["weights"]), len(req["domain"]["profiles"]), result["generator_count"]
    base = req["domain"]["base_index"]
    perm = req["permutation"]
    inverse = [perm.index(j) for j in range(n)]
    defs = [f"def weights : Fin {n} → ℤ := {lean_vector(req['weights'])}",
            f"def scalars : Fin {n} → ℤ := {lean_vector(req['scalar_valuations'])}",
            f"def profiles : Fin {m} → Fin {n} → ℤ := {lean_vector(req['domain']['profiles'])}",
            f"def generators : Fin {r} → Fin {n} → ℤ := {lean_vector(result['generators'])}",
            f"def genCoeffs : Fin {m} → Fin {r} → ℤ := {lean_vector(result['hgen_coefficients'])}",
            f"def memCoeffs : Fin {r} → Fin {m} → ℤ := {lean_vector(result['hmem_coefficients'])}"]
    code = f"""import Candidates.LedgerTool
-- Generated from the explicit request. Emission is not verification.
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
open scoped BigOperators
namespace GeneratedLedger
open IUTBridge.Slots IUTBridge.WeightedLedger Candidates.RestrictedLedger Candidates.LedgerTool
instance : Fact (Nat.Prime {p}) := ⟨by decide⟩
{chr(10).join(defs)}
def permutation : Equiv.Perm (Fin {n}) where
  toFun := {lean_vector(perm)}
  invFun := {lean_vector(inverse)}
  left_inv := by decide
  right_inv := by decide

theorem span_generation : ∀ k, profiles k - profiles {base} =
    ∑ i, genCoeffs k i • generators i := by decide
theorem span_membership : ∀ i, generators i =
    ∑ k, memCoeffs i k • (profiles k - profiles {base}) := by decide
theorem domain_nonempty : powerTuple {p} (profiles {base}) ∈ profileDomain {p} profiles :=
  powerTuple_mem {p} profiles {base}
theorem scalars_nonzero : ∀ j, powerTuple {p} scalars j ≠ 0 := powerTuple_ne_zero {p} scalars

theorem numeric_result :
    (fun j => weights (permutation j) - weights j) = ({lean_vector(result['d'])} : Fin {n} → ℤ) ∧
    (∑ j, weights (permutation j) * scalars j) = {result['scalar_budget']} ∧
    (dot (fun j => weights (permutation j) - weights j) (profiles {base}) +
      ∑ j, weights (permutation j) * scalars j) = {result['base_equation']} ∧
    (fun k => transformProfile permutation scalars (profiles k)) =
      ({lean_vector(result['image_profiles'])} : Fin {m} → Fin {n} → ℤ) ∧
    (fun k => dot (fun j => weights (permutation j) - weights j) (profiles k) +
      ∑ j, weights (permutation j) * scalars j) = ({lean_vector(result['profile_shifts'])} : Fin {m} → ℤ) ∧
    (fun i => dot (fun j => weights (permutation j) - weights j) (generators i)) =
      ({lean_vector(result['generator_values'])} : Fin {r} → ℤ) := by decide
"""
    if result["ledger_preserved"]:
        code += f"""
theorem ledger_result : ∀ x ∈ profileDomain {p} profiles,
    weightedLedger {p} weights (relabel {p} permutation (slotwise {p} (powerTuple {p} scalars) x)) =
      weightedLedger {p} weights x :=
  (finite_criterion {p} profiles {base} weights scalars permutation generators genCoeffs memCoeffs
    span_generation span_membership).mpr (by decide)
"""
    else:
        k = result["witness"]["profile_index"]
        code += f"""
theorem ledger_result : powerTuple {p} (profiles {k}) ∈ profileDomain {p} profiles ∧
    weightedLedger {p} weights
      (relabel {p} permutation (slotwise {p} (powerTuple {p} scalars) (powerTuple {p} (profiles {k})))) ≠
      weightedLedger {p} weights (powerTuple {p} (profiles {k})) :=
  ledger_counterexample {p} profiles {k} weights scalars permutation (by decide)
"""
    domain_prop = f"∀ x ∈ profileDomain {p} profiles, relabel {p} permutation (slotwise {p} (powerTuple {p} scalars) x) ∈ profileDomain {p} profiles"
    if result["domain_invariant"]:
        code += f"\ntheorem domain_result : {domain_prop} :=\n  (domain_invariant_iff {p} profiles scalars permutation).mpr (by decide)\n"
    else:
        code += f"\ntheorem domain_result : ¬ ({domain_prop}) := by\n  intro h\n  have hf := (domain_invariant_iff {p} profiles scalars permutation).mp h\n  exact (by decide : ¬ ∀ k, ∃ l, transformProfile permutation scalars (profiles k) = profiles l) hf\n"
    names = ["span_generation", "span_membership", "domain_nonempty", "scalars_nonzero", "numeric_result", "ledger_result", "domain_result"]
    if not result["ledger_preserved"]:
        witness = result["witness"]
        k = witness["profile_index"]
        before = f"weightedLedger {p} weights (powerTuple {p} (profiles {k}))"
        after = f"weightedLedger {p} weights (relabel {p} permutation (slotwise {p} (powerTuple {p} scalars) (powerTuple {p} (profiles {k}))))"
        code += f"""
theorem witness_values :
    {before} = {witness['ledger_before']} ∧
    {after} = {witness['ledger_after']} ∧
    {after} - {before} = {witness['ledger_shift']} := by
  simp only [weightedLedger_powerTuple, weightedLedger_transformed_powerTuple]
  decide
"""
        names.append("witness_values")
    if not result["domain_invariant"]:
        k = result["domain_witness"]["profile_index"]
        code += f"""
theorem domain_witness_result : powerTuple {p} (profiles {k}) ∈ profileDomain {p} profiles ∧
    relabel {p} permutation (slotwise {p} (powerTuple {p} scalars) (powerTuple {p} (profiles {k}))) ∉
      profileDomain {p} profiles :=
  domain_counterexample {p} profiles scalars permutation {k} (by decide)
"""
        names.append("domain_witness_result")
    code += "\nend GeneratedLedger\n" + "".join(f"#print axioms GeneratedLedger.{name}\n" for name in names)
    return code, [f"GeneratedLedger.{name}" for name in names]


def write_json(path, data):
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def emit(input_path, out):
    out = Path(out).resolve()
    out.mkdir(parents=True, exist_ok=True)
    # Remove stale certification material when reusing an output directory.
    for name in ("certificate.lean", "manifest.json"):
        (out / name).unlink(missing_ok=True)
    raw = None
    try:
        raw = json.loads(Path(input_path).read_text(encoding="utf-8-sig"))
        req = validate(raw)
        result = calculate(req)
        code, names = certificate(req, result)
        write_json(out / "request.json", req)
        (out / "certificate.lean").write_text(code, encoding="utf-8")
        proposed = {"schema": 1, "status": "PROPOSED", "result": result}
        write_json(out / "result.json", proposed)
        manifest = {"schema": 1, "component": "restricted-ledger", "status": "PROPOSED",
                    "project": str(Path(__file__).resolve().parent.parent),
                    "prepare_target": "Candidates.LedgerTool", "certificate": str(out / "certificate.lean"),
                    "theorem_names": names, "result": result,
                    "request_sha256": hashlib.sha256((out / "request.json").read_bytes()).hexdigest(),
                    "certificate_sha256": hashlib.sha256((out / "certificate.lean").read_bytes()).hexdigest()}
        write_json(out / "manifest.json", manifest)
        return {**proposed, "manifest": str(out / "manifest.json")}, 0
    except Insufficient as error:
        result = {"schema": 1, "status": "INSUFFICIENT", "reason": str(error)}
    except (InputError, json.JSONDecodeError, UnicodeError, OSError) as error:
        result = {"schema": 1, "status": "INVALID_INPUT", "reason": str(error)}
    write_json(out / "request.json", raw)
    write_json(out / "result.json", result)
    (out / "certificate.lean").write_text("-- No mathematical certificate: " + result["status"] + "\n", encoding="utf-8")
    write_json(out / "manifest.json", {"schema": 1, "component": "restricted-ledger",
        "status": result["status"], "project": str(Path(__file__).resolve().parent.parent),
        "prepare_target": "Candidates.LedgerTool", "certificate": str(out / "certificate.lean"),
        "theorem_names": [], "result": result,
        "request_sha256": hashlib.sha256((out / "request.json").read_bytes()).hexdigest(),
        "certificate_sha256": hashlib.sha256((out / "certificate.lean").read_bytes()).hexdigest()})
    return result, 2


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True)
    parser.add_argument("--out", required=True)
    args = parser.parse_args(argv)
    try:
        result, code = emit(args.input, args.out)
    except OSError as error:
        result, code = {"schema": 1, "status": "INVALID_INPUT", "reason": str(error)}, 2
    print(json.dumps(result, ensure_ascii=False))
    return code


if __name__ == "__main__":
    sys.exit(main())
