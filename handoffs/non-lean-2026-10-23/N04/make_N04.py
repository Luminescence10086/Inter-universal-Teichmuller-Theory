#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""N04 signature extractor (static only; never runs Lean/Lake/LSP).

Extracts signature blocks *verbatim* from the fixed external repo files
(commit f7ed1cc8ea33234ec66b1f49fb9e12212742cdcb) and writes signatures.csv.
No file outside handoffs/non-lean-2026-10-23/N04/ is written.
"""
import csv
import hashlib
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[2]                     # workspace root
N04 = HERE

REPO_REL = "reviews/core-round/external/iut"

SIGS = [
    dict(
        id="S1",
        lean_name="Iut.LocalConstruct.orderSubmodule (+ Iut.LocalConstruct.order)",
        kind="def",
        rel=f"{REPO_REL}/Iut/Concrete/LocalConstruct/Integral.lean",
        line_start=206,
        line_end=209,
        assumptions=(
            "binders: {K : Type u} [Field K] [NumberField K] {ι : Type} [Fintype ι] "
            "(p : Nat.Primes) (c : ι → Place K) [Integral.lean:43, :175]; "
            "no ramification/finiteness hypothesis; "
            "depends on def integralSet/tprodIntegral (Integral.lean:178-185) and on the "
            "ℤ_p-algebra structure instAlgebraPadicIntTensor (Integral.lean:189-193, "
            "restriction of scalars along ℤ_p → ℚ_p). "
            "Result: Submodule ℤ_[p] (Tensor K (.finite p) c), the ℤ_p-span of integralSet."
        ),
        source_claim_supported=(
            "SOURCE_FACT: the 'tensor order' is defined as the ℤ_p-span of the image of "
            "integral elementary tensors; the docstring's identification with the image of "
            "⊗_{ℤ_p} 𝓞_{c j} is prose only — no isomorphism with an abstract tensor-product "
            "ring is stated in Lean ⇒ faithfulness of the name UNRESOLVED; "
            "do not read this as an integral closure (that is S2)."
        ),
        status="SOURCE_FACT",
    ),
    dict(
        id="S2",
        lean_name="Iut.LocalConstruct.integral",
        kind="def",
        rel=f"{REPO_REL}/Iut/Concrete/LocalConstruct/MaximalOrder.lean",
        line_start=181,
        line_end=185,
        assumptions=(
            "binders: {K : Type u} [Field K] [NumberField K] {ι : Type} [Fintype ι] "
            "(p : Nat.Primes) (c : ι → Place K) [MaximalOrder.lean:57, :96]; "
            "no extra hypothesis; definition is Mathlib integralClosure ℤ_[p] "
            "(Tensor K (.finite p) c), needing only the ℤ_p-algebra structure "
            "(Integral.lean:189-193). Result is a Set; the only additive packaging is "
            "integralAddSubgroup (MaximalOrder.lean:323-324)."
        ),
        source_claim_supported=(
            "SOURCE_FACT: the maximal order (R_I)^∼ is *defined* as the integral closure of "
            "ℤ_p in the packet, so it is not the tensor order; only order_subset_integral "
            "(MaximalOrder.lean:191) is proved, strictness/equality is not. "
            "The identification with IUT IV Prop. 1.2 appears in the docstring only "
            "(prose), so text faithfulness is UNRESOLVED."
        ),
        status="SOURCE_FACT",
    ),
    dict(
        id="S3",
        lean_name="Iut.LocalConstruct.residueEquiv",
        kind="def",
        rel=f"{REPO_REL}/Iut/Concrete/LocalConstruct/ResidueField.lean",
        line_start=72,
        line_end=75,
        assumptions=(
            "binders: {K : Type u} [Field K] [NumberField K] {ι : Type} [Fintype ι] "
            "(p : Nat.Primes) (c : ι → Place K) [ResidueField.lean:44-45]; "
            "needs IsArtinianRing and IsReduced instances on the packet "
            "(MaximalOrder.lean:235 isArtinianRing_tensor, :104 isReduced_tensor) so that "
            "Mathlib's IsArtinianRing.equivPi applies; base ring is the packet itself "
            "(≃ₐ[Tensor K (.finite p) c])."
        ),
        source_claim_supported=(
            "SOURCE_FACT: a *ring-level* algebra equivalence onto the finite product of "
            "residue fields (indices = MaximalSpectrum), not merely a ℚ_p-linear iso, and "
            "not a decomposition into the local-field factors ∏_j K_{c j}; "
            "a factor-wise product decomposition has no signature in this repo ⇒ "
            "'ambient tensor algebra → product of local fields' UNRESOLVED."
        ),
        status="SOURCE_FACT",
    ),
    dict(
        id="S4",
        lean_name="Iut.LocalConstruct.mem_integral_iff_forall_resNorm_le_one",
        kind="theorem",
        rel=f"{REPO_REL}/Iut/Concrete/LocalConstruct/ResidueField.lean",
        line_start=193,
        line_end=197,
        assumptions=(
            "binders as in S3 plus (m : MaximalSpectrum (Tensor K (.finite p) c)) "
            "[ResidueField.lean:53]; resNorm := spectralNorm ℚ_[p] (ResidueField p c m) "
            "(ResidueField.lean:89-90), proj := Ideal.Quotient.mkₐ (ResidueField.lean:66-67); "
            "uses mem_integral_iff_forall_isIntegral (:172-173) and "
            "isIntegral_iff_resNorm_le_one (:125-126); no extra hypothesis."
        ),
        source_claim_supported=(
            "SOURCE_FACT: the order/decomposition correspondence is given pointwise as a "
            "norm criterion (x ∈ (R_I)^∼ ↔ ∀ 𝔪, ‖x mod 𝔪‖ ≤ 1); the docstring calls this "
            "'the product of the closed unit balls', but no statement identifies (R_I)^∼ "
            "with the image of a product subring under residueEquiv ⇒ ring-level "
            "correspondence UNRESOLVED."
        ),
        status="SOURCE_FACT",
    ),
]

FIELDS = [
    "id", "lean_name", "kind", "file", "line_start", "line_end",
    "file_sha256", "verbatim_sha256", "signature_verbatim",
    "assumptions", "source_claim_supported", "status",
]


def sha256_file(p: pathlib.Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main() -> int:
    rows = []
    for s in SIGS:
        path = ROOT / s["rel"]
        lines = path.read_text(encoding="utf-8").splitlines()
        block = "\n".join(lines[s["line_start"] - 1:s["line_end"]])
        rows.append({
            "id": s["id"],
            "lean_name": s["lean_name"],
            "kind": s["kind"],
            "file": s["rel"],
            "line_start": s["line_start"],
            "line_end": s["line_end"],
            "file_sha256": sha256_file(path),
            "verbatim_sha256": hashlib.sha256(block.encode("utf-8")).hexdigest(),
            "signature_verbatim": block,
            "assumptions": s["assumptions"],
            "source_claim_supported": s["source_claim_supported"],
            "status": s["status"],
        })

    out = N04 / "signatures.csv"
    with out.open("w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=FIELDS, lineterminator="\n")
        w.writeheader()
        w.writerows(rows)

    print(f"wrote {out} ({len(rows)} signatures, {out.stat().st_size} bytes)")
    for r in rows:
        print(f"  {r['id']} {r['lean_name']}")
        print(f"     {r['file']}:{r['line_start']}-{r['line_end']}")
        print(f"     file_sha256={r['file_sha256']}")
        print(f"     verbatim_sha256={r['verbatim_sha256']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
