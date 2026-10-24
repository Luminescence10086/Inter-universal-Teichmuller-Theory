#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""T065 · field-level provenance tracer for the Kummer environments.

Read-only. Emits machine-checkable provenance rows: for every environment field we
record whether the value is
  DEF_GEN   -- produced by a definition/theorem body inside the checkout (construction),
  FIELD     -- supplied by a structure field (declared, never built),
  TAUT      -- produced only by a `taut`/`trivial`/`refl` degenerate exhibit,
  NONE      -- no producer found anywhere in the checkout.

Criterion (per task card): a field is "DEF_GEN" only when a declaration in the
checkout has the field's value type as its *result type* and its body actually
constructs that value. Merely sharing a field NAME (e.g. `kum`) is never evidence.

Usage: python trace_fields.py --root <repo> [--json out.json]
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys

IUT = os.path.join("reviews", "core-round", "external", "iut")

# (file, structure, field, kind, producer, note)
# kind is one of DEF_GEN / FIELD / TAUT / NONE; producer is the exact declaration
# name whose result type is the field value, or "-" when there is none.
ROWS = [
    # ---- StripKummer (Iut/LogLink/StripKummer.lean:168-178) ----
    ("reviews/core-round/external/iut/Iut/LogLink/StripKummer.lean", "StripKummer", "strip",
     "FIELD", "-",
     "ℤ×ℤ → RigidDGalStrip D. Vnon/DGalStrip/rigidification exist, but no declaration has "
     "result type `ℤ×ℤ → RigidDGalStrip D`; LogThetaLattice.H : ℤ×ℤ → ThetaPmEllNFHT D is a "
     "different endpoint (theaters, not strips)."),
    ("reviews/core-round/external/iut/Iut/LogLink/StripKummer.lean", "StripKummer", "coric",
     "FIELD", "-",
     "RigidDGalStrip D. Only `RigidDGalStrip.taut D` (degenerate) produces one; no coric strip "
     "of a column/vertex is constructed."),
    ("reviews/core-round/external/iut/Iut/LogLink/StripKummer.lean", "StripKummer", "link",
     "FIELD", "-",
     "∀ a, (strip a).strip.Iso coric.strip. PrimeStrip.nonempty_iso proves inhabitation of "
     "P.Iso Q for ANY two strips, so this field is *provably fillable but arbitrary* -- it "
     "carries no source information."),
    ("reviews/core-round/external/iut/Iut/LogLink/StripKummer.lean", "StripKummer", "kum",
     "FIELD", "-",
     "ℤ×ℤ → Scaling D. No producer: Scaling is itself a structure whose `u` field is arbitrary."),
    ("reviews/core-round/external/iut/Iut/LogLink/StripKummer.lean", "StripKummer", "scale",
     "FIELD", "-",
     "∀ a, StripScaling D (RigidDGalStrip.gal (link a)) (kum a). This is the *coupling* "
     "equation: it ties kum to gal(link). It is an input, not derived from strip/coric/link/kum."),
    # ---- RigidDGalStrip (Iut/HodgeTheater/StripLift.lean:428) ----
    ("reviews/core-round/external/iut/Iut/HodgeTheater/StripLift.lean", "RigidDGalStrip", "strip",
     "FIELD", "-",
     "DGalStrip D := PrimeStrip (dGalKind D) (locGalModel D). `PrimeStrip.tautological` produces "
     "the degenerate member only; no theater-derived strip is constructed."),
    ("reviews/core-round/external/iut/Iut/HodgeTheater/StripLift.lean", "RigidDGalStrip", "kappa",
     "FIELD", "-",
     "∀ w, carrier ≃ₜ* LocGal (D.V.sectFin w). The rigidification κ_v is the Kummer structure; "
     "only `taut` supplies `ContinuousMulEquiv.refl`."),
    # ---- GalKummer (Iut/LogLink/GalKummer.lean:368) ----
    ("reviews/core-round/external/iut/Iut/LogLink/GalKummer.lean", "GalKummer", "kum",
     "FIELD", "-", "identical field name and type as StripKummer.kum; no producer."),
    ("reviews/core-round/external/iut/Iut/LogLink/GalKummer.lean", "GalKummer", "gal",
     "FIELD", "-",
     "∀ a, GalInducedScaling D (kum a). Existential in the inducing φ (FactorGalInduced). "
     "Filled only by `galInducedScaling_one` (degenerate)."),
    # ---- AnabelianKummer (GalKummer.lean:361) ----
    ("reviews/core-round/external/iut/Iut/LogLink/GalKummer.lean", "AnabelianKummer", "kum",
     "FIELD", "-", "no producer."),
    ("reviews/core-round/external/iut/Iut/LogLink/GalKummer.lean", "AnabelianKummer", "anab",
     "FIELD", "-", "no producer beyond `unitInducedScaling_one` / `anabelianScaling_negScale`."),
    # ---- LatticeKummer (Iut/LogLink/Kummer.lean:248) ----
    ("reviews/core-round/external/iut/Iut/LogLink/Kummer.lean", "LatticeKummer", "kum",
     "FIELD", "-", "no producer."),
    ("reviews/core-round/external/iut/Iut/LogLink/Kummer.lean", "LatticeKummer", "unit",
     "FIELD", "-",
     "∀ a, UnitInducedScaling D (kum a). The whole point of GalKummer/StripKummer is to supply "
     "this field from an origin; in LatticeKummer itself it is an input."),
    # ---- fields that ARE discharged by a definition (derived) ----
    ("reviews/core-round/external/iut/Iut/LogLink/GalKummer.lean", "GalKummer", "<toAnabelianKummer>",
     "DEF_GEN", "GalKummer.toAnabelianKummer",
     "DEF_GEN: `anab` of the produced AnabelianKummer is built from `(K.gal a).anabelian` "
     "(theorem GalInducedScaling.anabelian)."),
    ("reviews/core-round/external/iut/Iut/LogLink/GalKummer.lean", "GalKummer", "<toLatticeKummer>",
     "DEF_GEN", "GalKummer.toLatticeKummer",
     "DEF_GEN: `unit` discharged via AnabelianScaling.unitInduced; but `kum` is copied, not built."),
    ("reviews/core-round/external/iut/Iut/LogLink/StripKummer.lean", "StripKummer", "<toGalKummer>",
     "DEF_GEN", "StripKummer.toGalKummer",
     "DEF_GEN: `gal` built from `(K.scale a).galInduced` (StripScaling.galInduced). The Galois "
     "witness stops being existential; `kum` is still copied from field `kum`."),
    ("reviews/core-round/external/iut/Iut/LogLink/StripKummer.lean", "StripKummer", "<gal>",
     "DEF_GEN", "StripKummer.gal",
     "DEF_GEN: `gal a w = RigidDGalStrip.gal (K.link a) w` -- genuinely computed from the strip "
     "isomorphism + rigidifications. This is the one real read-off in the file."),
    ("reviews/core-round/external/iut/Iut/LogLink/StripKummer.lean", "StripKummer", "<liftIso>",
     "DEF_GEN", "StripKummer.liftIso",
     "DEF_GEN: RigidDGalStrip.liftIso (K.link a); Frobenioid part = galFrobAt D w (gal (link a))."),
    # ---- StripScaling consumers ----
    ("reviews/core-round/external/iut/Iut/LogLink/StripKummer.lean", "<StripScaling>", "<galInduced>",
     "DEF_GEN", "StripScaling.galInduced",
     "DEF_GEN: from the *given* per-factor b with compGalLogEquiv φ = scale b, rebuilds the "
     "existential GalInducedScaling. Pure repackaging: no new construction of b."),
    ("reviews/core-round/external/iut/Iut/LogLink/StripKummer.lean", "<StripScaling>", "<shift_eq_zero>",
     "DEF_GEN", "StripScaling.shift_eq_zero",
     "DEF_GEN: distortion vanishing follows from galInduced.anabelian.shift_eq_zero; does NOT "
     "produce the scalings."),
]

# Per-factor producer: the only place a factor scaling b is actually CONSTRUCTED.
SCALING_PRODUCERS = [
    ("reviews/core-round/external/iut/Iut/LogLink/GalKummer.lean",
     "exists_factorGalInduced_of_linear",
     "CONDITIONAL",
     "Given hov : IsOver K p v, φ : CompGal ≃ₜ*, and hlin : the induced ψ is K_v-linear, "
     "produces b := Units.mk0 (ψ 1) with ψ = scale b. The linearity hlin is the real input: "
     "it says the identification induced by φ is a scaling at all."),
    ("reviews/core-round/external/iut/Iut/LogLink/GalKummer.lean",
     "factorGalInduced_one", "TAUT", "b = 1, φ = refl."),
    ("reviews/core-round/external/iut/Iut/LogLink/GalKummer.lean",
     "factorUnitsAut_neg_one", "TAUT", "b = -1, β = MulEquiv.inv (the alien x ↦ -x)."),
    ("reviews/core-round/external/iut/Iut/LogLink/Kummer.lean",
     "factorUnitInduced_one", "TAUT", "b = 1."),
    ("reviews/core-round/external/iut/Iut/LogLink/Kummer.lean",
     "factorUnitInduced_neg_one", "TAUT", "b = -1."),
]

# Consumers: every place that READS a Kummer environment field.
# `decl` is the identifier AS WRITTEN in the source (namespaces are implicit there).
CONSUMERS = [
    ("reviews/core-round/external/iut/Iut/LogLink/StripKummer.lean", "gal",
     "K.link", "reads link -> RigidDGalStrip.gal"),
    ("reviews/core-round/external/iut/Iut/LogLink/StripKummer.lean", "toGalKummer",
     "K.kum, K.scale", "copies kum, converts scale"),
    ("reviews/core-round/external/iut/Iut/LogLink/StripKummer.lean", "toLatticeKummer",
     "via toGalKummer", "unit field discharged"),
    ("reviews/core-round/external/iut/Iut/LogLink/StripKummer.lean", "kum_ne_qScale_zpow",
     "K.kum", "uses kum through toGalKummer's anabelian obstruction"),
    ("reviews/core-round/external/iut/Iut/LogLink/StripKummer.lean", "liftIso",
     "K.link", "lifts to F^⊢"),
    ("reviews/core-round/external/iut/Iut/LogLink/StripKummer.lean", "liftIso_functor",
     "K.link via gal", "Frobenioid functor equality, rfl"),
    ("reviews/core-round/external/iut/Iut/LogLink/StripKummer.lean", "trivial",
     "RigidDGalStrip.taut + Iso.refl + 1", "degenerate exhibit only"),
    ("reviews/core-round/external/iut/Iut/LogLink/StripKummer.lean", "forget_liftIso",
     "K.link", "rfl"),
    ("reviews/core-round/external/iut/Iut/LogLink/StripKummer.lean", "xi_iff_ss",
     "K.toGalKummer", "statement only, via SSIneq"),
    ("reviews/core-round/external/iut/Iut/LogLink/Kummer.lean", "model",
     "K.kum", "builds MultiContainer"),
    ("reviews/core-round/external/iut/Iut/LogLink/Kummer.lean", "distortion_eq_zero",
     "K.unit via model", "volume neutrality"),
    ("reviews/core-round/external/iut/Iut/LogLink/Kummer.lean", "toLinkedChain",
     "K.kum, K.logShellCompat", "row restriction"),
    ("reviews/core-round/external/iut/Iut/LogLink/Thm311.lean", "XiPrinciple",
     "K.toLatticeKummer", "statement only"),
]

DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+)?"
    r"(structure|def|theorem|lemma|abbrev|instance|class)\s+([A-Za-z_][\w.']*)",
)
FIELD_RE = re.compile(r"^\s{2}([A-Za-z_][\w']*)\s*:\s")


def sha256(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def actual_fields(root: str, rel: str, struct: str):
    """Re-read the structure body so the report cannot drift from the source."""
    path = os.path.join(root, rel)
    if not os.path.exists(path):
        return None
    with open(path, encoding="utf-8") as fh:
        lines = fh.read().splitlines()
    start = None
    for i, line in enumerate(lines):
        if re.match(rf"^\s*structure\s+{re.escape(struct)}\b", line):
            start = i
            break
    if start is None:
        return None
    out = []
    for line in lines[start + 1:]:
        if re.match(r"^\s*(namespace|end|section)\b", line):
            break
        m = FIELD_RE.match(line)
        if m:
            out.append(m.group(1))
        if re.match(r"^\S", line) and out:
            break
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".")
    ap.add_argument("--json")
    args = ap.parse_args()
    root = os.path.abspath(args.root)

    report = {"rows": [], "scaling_producers": [], "consumers": [], "struct_fields": {}}

    for rel, struct, field, kind, producer, note in ROWS:
        path = os.path.join(root, rel)
        exists = os.path.exists(path)
        report["rows"].append({
            "file": rel,
            "structure": struct,
            "field": field,
            "kind": kind,
            "producer": producer,
            "note": note,
            "file_present": exists,
            "file_sha256": sha256(path) if exists else None,
        })

    for rel, name, kind, note in SCALING_PRODUCERS:
        path = os.path.join(root, rel)
        present = False
        if os.path.exists(path):
            with open(path, encoding="utf-8") as fh:
                present = re.search(rf"\b{re.escape(name)}\b", fh.read()) is not None
        report["scaling_producers"].append(
            {"file": rel, "decl": name, "kind": kind, "note": note, "found_in_source": present})

    for rel, decl, fields, note in CONSUMERS:
        path = os.path.join(root, rel)
        present = False
        if os.path.exists(path):
            with open(path, encoding="utf-8") as fh:
                present = re.search(rf"\b{re.escape(decl)}\b", fh.read()) is not None
        report["consumers"].append(
            {"file": rel, "decl": decl, "fields_read": fields, "note": note,
             "found_in_source": present})

    for rel in sorted({r[0] for r in ROWS}):
        path = os.path.join(root, rel)
        if not os.path.exists(path):
            continue
        with open(path, encoding="utf-8") as fh:
            text_src = fh.read()
        # Confirm every claimed DEF_GEN producer is a real declaration in that file.
        for r in report["rows"]:
            if r["file"] != rel or r["kind"] != "DEF_GEN":
                continue
            bare = r["producer"].rsplit(".", 1)[-1]
            r["producer_is_decl"] = bool(
                re.search(rf"^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?"
                          rf"(?:structure|def|theorem|lemma|abbrev)\s+{re.escape(bare)}\b",
                          text_src, re.M))
            r["producer_occurrences"] = len(re.findall(rf"\b{re.escape(bare)}\b", text_src))
    for rel, struct in [("reviews/core-round/external/iut/Iut/LogLink/StripKummer.lean", "StripKummer"),
                        ("reviews/core-round/external/iut/Iut/HodgeTheater/StripLift.lean", "RigidDGalStrip"),
                        ("reviews/core-round/external/iut/Iut/LogLink/GalKummer.lean", "GalKummer"),
                        ("reviews/core-round/external/iut/Iut/LogLink/Kummer.lean", "LatticeKummer")]:
        report["struct_fields"][struct] = actual_fields(root, rel, struct)

    counts = {}
    for r in report["rows"]:
        counts[r["kind"]] = counts.get(r["kind"], 0) + 1
    report["counts"] = counts

    text = json.dumps(report, ensure_ascii=False, indent=2)
    if args.json:
        with open(args.json, "w", encoding="utf-8") as fh:
            fh.write(text + "\n")
    # Console: compact, encoding-safe (Windows consoles are GBK).
    summary = {
        "counts": report["counts"],
        "struct_fields": report["struct_fields"],
        "files_present": all(r["file_present"] for r in report["rows"]),
        "def_gen_producers_are_decls": [
            {"producer": r["producer"], "ok": r.get("producer_is_decl"),
             "occurrences": r.get("producer_occurrences")}
            for r in report["rows"] if r["kind"] == "DEF_GEN"],
        "consumers_found": sum(1 for x in report["consumers"] if x["found_in_source"]),
        "consumers_total": len(report["consumers"]),
        "scaling_producers_found": sum(
            1 for x in report["scaling_producers"] if x["found_in_source"]),
        "scaling_producers_total": len(report["scaling_producers"]),
    }
    out = json.dumps(summary, ensure_ascii=False, indent=2)
    enc = sys.stdout.encoding or "utf-8"
    sys.stdout.write(out.encode(enc, "replace").decode(enc) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
