#!/usr/bin/env python3
"""Finite orbit hull calculator. Emits proposals; only the shared Lean runner verifies."""
import argparse
import hashlib
import json
import math
from pathlib import Path
import sys

LIMITS = {"max_n": 16, "max_permutations": 128, "max_N": 10000,
          "max_p": 2147483647, "max_input_bytes": 1048576}


class InputError(ValueError):
    pass


def integer(value, label, lo, hi):
    if type(value) is not int or not lo <= value <= hi:
        raise InputError(f"{label} must be an integer in [{lo}, {hi}]")
    return value


def unique_object(pairs):
    out = {}
    for key, value in pairs:
        if key in out:
            raise InputError(f"duplicate JSON key: {key}")
        out[key] = value
    return out


def validate(data):
    required = {"schema", "p", "N", "thresholds", "permutations"}
    if type(data) is not dict or not required <= data.keys() or data.keys() - required - {"require_enlargement"}:
        raise InputError("expected only schema, p, N, thresholds, permutations, and optional require_enlargement")
    integer(data["schema"], "schema", 1, 1)
    p = integer(data["p"], "p", 2, LIMITS["max_p"])
    if any(p % d == 0 for d in range(2, math.isqrt(p) + 1)):
        raise InputError("p must be prime (input-domain rejection, not a mathematical counterexample)")
    N = integer(data["N"], "N", 0, LIMITS["max_N"])
    k = data["thresholds"]
    if type(k) is not list or not 1 <= len(k) <= LIMITS["max_n"]:
        raise InputError("thresholds must be an array with 1..16 coordinates")
    n = len(k)
    for j, value in enumerate(k):
        integer(value, f"thresholds[{j}]", 0, N)
    perms = data["permutations"]
    if type(perms) is not list or not 1 <= len(perms) <= LIMITS["max_permutations"]:
        raise InputError("permutations must contain 1..128 permutations")
    for i, perm in enumerate(perms):
        if type(perm) is not list or len(perm) != n:
            raise InputError(f"permutations[{i}] must have dimension {n}")
        for v in perm:
            integer(v, f"permutations[{i}] entry", 0, n - 1)
        if sorted(perm) != list(range(n)):
            raise InputError(f"permutations[{i}] is not a bijection")
    req = data.get("require_enlargement", True)
    if type(req) is not bool:
        raise InputError("require_enlargement must be a JSON boolean")
    if req and list(range(n)) not in perms:
        raise InputError("require_enlargement=true requires the identity in permutations")
    return dict(data, require_enlargement=req)


def compute(data):
    k, perms = data["thresholds"], data["permutations"]
    n, N, p = len(k), data["N"], data["p"]
    inverses = [[perm.index(j) for j in range(n)] for perm in perms]
    witnesses = []
    hull = []
    for j in range(n):
        i = min(range(len(perms)), key=lambda i: (k[inverses[i][j]], i))
        hull.append(k[inverses[i][j]])
        witnesses.append({"permutation_index": i, "source_coordinate": inverses[i][j]})
    box_exp, hull_exp = sum(N - v for v in k), sum(N - v for v in hull)
    enlargement = sum(v - h for v, h in zip(k, hull)) if data["require_enlargement"] else None
    return {"hull_thresholds": hull, "witnesses": witnesses,
            "box_exponent": box_exp, "hull_exponent": hull_exp,
            "enlargement_exponent": enlargement,
            "cardinality": {"base": p, "box_exponent": box_exp, "hull_exponent": hull_exp, "ratio_exponent": enlargement},
            "action": "A_sigma(x)[j]=x[sigma_inverse[j]]",
            "domain": {"n": n, "p": p, "N": N, "permutation_count": len(perms),
                       "nonempty": True, "prime": True, "thresholds_bounded": True,
                       "has_identity": list(range(n)) in perms, "require_enlargement": data["require_enlargement"]}}


def vec(values):
    return "![" + ", ".join(map(str, values)) + "]"


def certificate(data, result):
    p, N, n, m = data["p"], data["N"], len(data["thresholds"]), len(data["permutations"])
    a, b = result["box_exponent"], result["hull_exponent"]
    names = ["input_valid", "action_convention", "witnesses_valid", "exponents_valid", "thresholds_eq_hull", "product_minimality", "cardinality"]
    lines = ["import Candidates.HullTool", "set_option autoImplicit false", "set_option maxRecDepth 100000", "set_option maxHeartbeats 4000000", "namespace HullToolCertificate", "open OrbitQuotient OrbitQuotient.HullTool", f"def k : Fin {n} → ℕ := {vec(data['thresholds'])}", f"def out : Fin {n} → ℕ := {vec(result['hull_thresholds'])}"]
    for i, perm in enumerate(data["permutations"]):
        inverse = [perm.index(j) for j in range(n)]
        lines.append(f"def perm{i} : Equiv.Perm (Fin {n}) := {{\n  toFun := {vec(perm)}\n  invFun := {vec(inverse)}\n  left_inv := by decide\n  right_inv := by decide\n}}")
    lines += [f"def perms : Fin {m} → Equiv.Perm (Fin {n}) := {vec(['perm'+str(i) for i in range(m)])}", "def gamma := family perms", "theorem gamma_nonempty : gamma.Nonempty := family_nonempty perms (by decide)", f"def witness : Fin {n} → Fin {m} := {vec([w['permutation_index'] for w in result['witnesses']])}", f"def source : Fin {n} → Fin {n} := {vec([w['source_coordinate'] for w in result['witnesses']])}", f"theorem input_valid : Nat.Prime {p} ∧ (∀ j, k j ≤ {N}) ∧ (∀ j, out j ≤ {N}) := by\n  refine ⟨by norm_num, by decide, by decide⟩", f"theorem action_convention : orbitUnion {p} {N} {n} gamma k =\n    ⋃ σ ∈ gamma, permAct {p} {N} σ.symm '' Box {p} {N} {n} k :=\n  orbitUnion_eq_inverse_images gamma k", "theorem witnesses_valid : ∀ j, (perms (witness j)).symm j = source j ∧\n    out j = k (source j) ∧ (∀ i, out j ≤ k ((perms i).symm j)) := by decide", f"theorem exponents_valid : (∑ j : Fin {n}, ({N} - k j)) = {a} ∧\n    (∑ j : Fin {n}, ({N} - out j)) = {b} := by decide", "theorem thresholds_eq_hull : out = hullThresh gamma gamma_nonempty k := by\n  apply checked_hull perms (by decide) k out\n  · exact fun j i => (witnesses_valid j).2.2 i\n  · intro j\n    exact ⟨witness j, by rw [(witnesses_valid j).1]; exact (witnesses_valid j).2.1⟩", f"theorem product_minimality : orbitUnion {p} {N} {n} gamma k ⊆ Box {p} {N} {n} out ∧\n    ∀ S : Fin {n} → Set (ZMod ({p} ^ {N})),\n      orbitUnion {p} {N} {n} gamma k ⊆ Set.pi Set.univ S →\n      Box {p} {N} {n} out ⊆ Set.pi Set.univ S := by\n  rw [thresholds_eq_hull]\n  exact hull_minimal_coordinateProduct gamma gamma_nonempty k", f"theorem cardinality : Nat.card ↥(Box {p} {N} {n} k) = {p} ^ {a} ∧\n    Nat.card ↥(Box {p} {N} {n} out) = {p} ^ {b} := by\n  constructor\n  · rw [box_cardinality input_valid.1 k input_valid.2.1, exponents_valid.1]\n  · rw [box_cardinality input_valid.1 out input_valid.2.2, exponents_valid.2]"]
    if data["require_enlargement"]:
        e = result["enlargement_exponent"]
        identity = data["permutations"].index(list(range(n)))
        lines += [f"theorem identity_mem : (1 : Equiv.Perm (Fin {n})) ∈ gamma := by\n  have h : perms ({identity} : Fin {m}) = 1 := by decide\n  rw [← h]\n  exact Finset.mem_image.mpr ⟨{identity}, Finset.mem_univ _, rfl⟩", f"theorem enlargement : (∑ j : Fin {n}, (k j - out j)) = {e} ∧\n    Nat.card ↥(Box {p} {N} {n} k) * {p} ^ {e} = Nat.card ↥(Box {p} {N} {n} out) := by\n  have he : (∑ j : Fin {n}, (k j - out j)) = {e} := by decide\n  refine ⟨he, ?_⟩\n  have hb := enlargement_budget_hull input_valid.1 gamma gamma_nonempty identity_mem k input_valid.2.1\n  rw [← thresholds_eq_hull, he] at hb\n  exact hb"]
        names += ["identity_mem", "enlargement"]
    lines += ["end HullToolCertificate", ""]
    return "\n".join(lines), ["HullToolCertificate." + name for name in names]


def encode(data):
    return (json.dumps(data, indent=2, ensure_ascii=True, sort_keys=True) + "\n").encode("utf-8")


def emit(input_path, out_dir):
    with Path(input_path).open("rb") as stream:
        raw = stream.read(LIMITS["max_input_bytes"] + 1)
    if len(raw) > LIMITS["max_input_bytes"]:
        raise InputError("input exceeds 1 MiB resource limit")
    data = validate(json.loads(raw.decode("utf-8-sig"), object_pairs_hook=unique_object,
                              parse_float=lambda x: (_ for _ in ()).throw(InputError("only integer JSON numbers are supported")),
                              parse_constant=lambda x: (_ for _ in ()).throw(InputError(f"non-finite JSON constant {x}"))))
    result = compute(data)
    cert, names = certificate(data, result)
    out = Path(out_dir).resolve()
    out.mkdir(parents=True, exist_ok=True)
    if any((out / name).exists() for name in ("request.json", "result.json", "certificate.lean", "manifest.json")):
        raise InputError("output contains existing artifacts; choose a fresh directory")
    request_bytes, cert_bytes = encode(data), cert.encode("utf-8")
    manifest = {"schema": 1, "component": "hull", "status": "PROPOSED",
                "project": str(Path(__file__).resolve().parents[1]), "prepare_target": "Candidates.HullTool",
                "certificate": str(out / "certificate.lean"), "theorem_names": names,
                "request_sha256": hashlib.sha256(request_bytes).hexdigest(),
                "certificate_sha256": hashlib.sha256(cert_bytes).hexdigest(),
                "domain": result["domain"], "result": result, "limits": LIMITS}
    (out / "request.json").write_bytes(request_bytes)
    (out / "certificate.lean").write_bytes(cert_bytes)
    (out / "result.json").write_bytes(encode({"status": "PROPOSED", **result}))
    (out / "manifest.json").write_bytes(encode(manifest))
    return manifest


def invalid_artifacts(input_path, out_dir, error):
    """Preserve rejected requests without emitting a theorem or a false counterexample."""
    out = Path(out_dir).resolve()
    out.mkdir(parents=True, exist_ok=True)
    if any((out / name).exists() for name in ("request.json", "result.json", "certificate.lean", "manifest.json")):
        return {"status": "INVALID_INPUT", "error": str(error), "mathematical_counterexample": False}
    try:
        with Path(input_path).open("rb") as stream:
            raw = stream.read(LIMITS["max_input_bytes"] + 1)
        request = json.loads(raw.decode("utf-8-sig"), object_pairs_hook=unique_object,
                             parse_float=lambda x: (_ for _ in ()).throw(InputError("non-integer JSON number")),
                             parse_constant=lambda x: (_ for _ in ()).throw(InputError(x)))
    except (ValueError, OSError, UnicodeError, RecursionError):
        request = {"unparsed_input": str(input_path)}
    result = {"status": "INVALID_INPUT", "error": str(error), "mathematical_counterexample": False}
    cert = b"-- INVALID_INPUT: no mathematical certificate was generated.\n"
    manifest = {"schema": 1, "component": "hull", "status": "INVALID_INPUT",
                "project": str(Path(__file__).resolve().parents[1]), "prepare_target": "Candidates.HullTool",
                "certificate": str(out / "certificate.lean"), "theorem_names": [],
                "request_sha256": hashlib.sha256(encode(request)).hexdigest(),
                "certificate_sha256": hashlib.sha256(cert).hexdigest(), "result": result}
    (out / "request.json").write_bytes(encode(request))
    (out / "result.json").write_bytes(encode(result))
    (out / "certificate.lean").write_bytes(cert)
    (out / "manifest.json").write_bytes(encode(manifest))
    return manifest


class JsonArgumentParser(argparse.ArgumentParser):
    def error(self, message):
        raise InputError(message)


def main(argv=None):
    parser = JsonArgumentParser(description=__doc__, add_help=False)
    parser.add_argument("--input", required=True)
    parser.add_argument("--out", required=True)
    args = None
    try:
        args = parser.parse_args(argv)
        result = emit(args.input, args.out)
    except (InputError, ValueError, OSError, UnicodeError, RecursionError) as exc:
        result = {"status": "INVALID_INPUT", "error": str(exc), "mathematical_counterexample": False}
        if args:
            try:
                result = invalid_artifacts(args.input, args.out, exc)
            except OSError as write_error:
                result["output_error"] = str(write_error)
        print(json.dumps(result, ensure_ascii=True))
        return 2
    print(json.dumps(result, ensure_ascii=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
