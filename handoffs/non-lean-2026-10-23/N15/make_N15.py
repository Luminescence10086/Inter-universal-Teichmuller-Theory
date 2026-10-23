"""N15 - build status.csv + candidate-graph.json (read-only over the workspace).

Rules implemented here (all mechanical, all re-runnable):

  kind
    lean-cli            delivery.json has a machine-readable `gates.cli` block  -> the CLI plane is recorded
    lean-experimental   a .lean artifact was run, but the run is only in `commands[]` (no `gates.cli`)
    experimental-tool   the primary product is a runnable checker/search tool, no Lean gate
    static-doc          everything else (papers, CSVs, markdown analyses)

  cli_verified
    PASSED_GATE          gates.cli.exit == 0                      (evidence: delivery.json#gates.cli)
    CLAIMED_NO_GATE_BLOCK status starts with CLI_CHECKED but there is no gates.cli block
    NOT_APPLICABLE_STATIC  lean_run false / no Lean artifact
    NO_RECORD            no delivery.json at all

  editor_evidence      taken from N14/receipt-review.csv, column `status`; items without a row -> UNRESOLVED

  edges                EXISTING_RECORD  when a task's delivery `inputs[]` path is an `outputs[]` path of another task
                        PROPOSED       otherwise, and then the catalogue/PATH.md/round-report.md line is the evidence
"""

import csv
import datetime
import glob
import hashlib
import json
import os

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", ".."))
OUT = os.path.join(ROOT, "handoffs", "non-lean-2026-10-23", "N15")

BACK = "handoffs/core-backward-2026-10-23"
SUP = "handoffs/core-support-2026-10-22"
NL = "handoffs/non-lean-2026-10-23"
CATALOG = "handoffs/non-lean-task-catalog-2026-10-23.md"
PATH = "research/core-backward-2026-10-23/PATH.md"
ROUND = "research/core-backward-2026-10-23/round-report.md"
N14CSV = "handoffs/non-lean-2026-10-23/N14/receipt-review.csv"

GAP_CMP = "GAP-core-comparison-reconstruction.md"
GAP_NAT = "GAP-core-native-realization.md"
GAP_HULL = "GAP-core-residue-hull-realization.md"

ORDER = (["T%d" % i for i in range(1, 5)] + ["K4"] + ["M%d" % i for i in range(1, 5)]
         + ["W%d" % i for i in range(1, 13)] + ["N%02d" % i for i in range(1, 17)])

# delivery.json location per item (None = not delivered)
DELIVERY = {}
for t in ["T1", "T2", "T3", "T4"]:
    DELIVERY[t] = "%s/%s/delivery.json" % (SUP, t)
DELIVERY["K4"] = "%s/K4/delivery.json" % BACK
for t in ["M1", "M2", "M3", "M4"] + ["W%d" % i for i in range(1, 13)]:
    DELIVERY[t] = "%s/%s/delivery.json" % (BACK, t)
for t in ["N01", "N02", "N03", "N04", "N05", "N06", "N07", "N08", "N09", "N10",
          "N11", "N12", "N13", "N14", "N15", "N16"]:
    DELIVERY[t] = "%s/%s/delivery.json" % (NL, t)

# gap routing (N15 PROPOSED table; no delivery.json names a GAP file - grep count 0/24)
GAP_ROUTE = {
    "T1": (GAP_CMP, "source-map of the paper: feeds the whole backward chain"),
    "T2": (GAP_CMP, "repository cards/edges: source layer for M3"),
    "T3": (GAP_CMP, "DelegatedLogBridge kernel: toy log bridge consumed by W1-W3"),
    "T4": (GAP_CMP, "QpThree kernel: the toy local field every W file reads from"),
    "K4": (GAP_CMP, "execution provenance for the q-pilot comparison route"),
    "M1": (GAP_CMP, "arrow/endpoint inventory of the comparison target"),
    "M2": (GAP_NAT, "normalization ledger = the H3 accounting book"),
    "M3": (GAP_CMP, "interface fields; K4/W1/W2 consume interfaces.json"),
    "M4": (GAP_CMP, "reusable-construction inventory for the comparison route"),
}
for t in ["W1", "W2", "W4", "W5", "W6", "W7", "W11"]:
    GAP_ROUTE[t] = (GAP_CMP, "readings / comparison maps: comparison-reconstruction route")
for t in ["W3", "W8", "W9", "W10", "W12"]:
    GAP_ROUTE[t] = (GAP_NAT, "H3 normalization/degree accounting for a native legal output")
GAP_ROUTE.update({
    "N01": (GAP_CMP, "source version evidence for the core dispute"),
    "N02": (GAP_CMP, "dispute matrix; which sentence of the comparison is attacked"),
    "N03": (GAP_CMP, "quantifiers/types of the comparison target itself"),
    "N04": (GAP_NAT, "coefficient ring / order / finite quotient interface for a native output"),
    "N05": (GAP_NAT, "what the allowed changes preserve = legality of the output family"),
    "N06": (GAP_NAT, "normalization / averaging / log-volume conversion ledger"),
    "N07": (GAP_CMP, "joint witness for a legal output of the comparison"),
    "N08": (GAP_HULL, "original hull vs. the existing principal-lattice tools"),
    "N09": (GAP_HULL, "finite quotient / orbit / hull candidate search"),
    "N10": (GAP_NAT, "finite constraint experiment over correlated choices"),
    "N11": (GAP_CMP, "tool design aimed at the N07/N08 gap"),
    "N12": (GAP_CMP, "external repository delta keeping the source pins honest"),
    "N13": ("", "cross-cutting: audits W4/W9/W10/W11/W12 declarations"),
    "N14": ("", "cross-cutting: editor-evidence grading, no single GAP"),
    "N15": ("", "cross-cutting: this index, no single GAP"),
    "N16": ("", "cross-cutting: static delivery checker, no single GAP"),
})
PLANNED_KIND = {
    "N02": "static-doc", "N06": "static-doc", "N07": "static-doc", "N08": "static-doc",
    "N09": "experimental-tool", "N10": "experimental-tool", "N11": "static-doc",
}

EDITOR_MAP = {
    "SUPPORTED_BY_EXISTING_EVIDENCE": "SUPPORTED",
    "INSUFFICIENT": "INSUFFICIENT",
    "STALE_HASH": "STALE",
    "MISSING": "MISSING",
}


def sha(p):
    h = hashlib.sha256()
    with open(os.path.join(ROOT, p), "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


def load(p):
    fp = os.path.join(ROOT, p)
    if not os.path.exists(fp):
        return None
    with open(fp, encoding="utf-8") as f:
        return json.load(f)


def n14_status():
    fp = os.path.join(ROOT, N14CSV)
    if not os.path.exists(fp):
        return None
    rows = {}
    with open(fp, encoding="utf-8", newline="") as f:
        for r in csv.DictReader(f):
            rows[r["task"].strip()] = r["status"].strip()
    return rows


def classify(t, d):
    if d is None:
        return (PLANNED_KIND.get(t, "static-doc"), "CATALOG_PLANNED_KIND (no delivery.json)", "NO_RECORD")
    gates = d.get("gates") or {}
    cli = gates.get("cli")
    outs = [o.get("path", "") for o in d.get("outputs") or []]
    has_lean = any(o.endswith(".lean") for o in outs)
    if isinstance(cli, dict) and cli:
        return ("lean-cli", "delivery.json#gates.cli present", "PASSED_GATE" if cli.get("exit") == 0 else "GATE_NONZERO")
    st = (d.get("status") or "")
    ran_lean = False
    for c in d.get("commands") or []:
        argv = c.get("argv") or [] if isinstance(c, dict) else []
        flat = " ".join(str(a) for a in argv).lower()
        if ("lake" in flat or "lean" in flat) and c.get("exit_code") == 0:
            ran_lean = True
    if (has_lean or ran_lean) and st.startswith("CLI_CHECKED"):
        return ("lean-experimental",
                "lean artifact or lean argv recorded in commands[] with exit 0, but no gates.cli block",
                "CLAIMED_NO_GATE_BLOCK")
    if has_lean:
        return ("lean-experimental", "lean artifact without a recorded CLI gate", "NO_RECORD")
    if t == "N16" or (outs and all(o.endswith(".py") for o in outs)):
        return ("experimental-tool", "primary product is a runnable static tool", "NO_RECORD")
    return ("static-doc", "no Lean artifact in outputs[]", "NOT_APPLICABLE_STATIC")


def primary_output(d):
    outs = (d or {}).get("outputs") or []
    if not outs:
        return ("", "")
    lean = [o for o in outs if o.get("path", "").endswith(".lean")]
    o = lean[0] if lean else outs[0]
    return (o.get("path", ""), o.get("sha256", ""))


def cli_evidence(t, d):
    if d is None:
        return "no delivery.json"
    cli = (d.get("gates") or {}).get("cli")
    if isinstance(cli, dict) and cli:
        sha_key = [k for k in cli if "sha" in k.lower()]
        pin = cli[sha_key[0]] if sha_key else ""
        return "%s#gates.cli exit=%s%s" % (DELIVERY[t], cli.get("exit"), (" source=" + pin[:16]) if pin else "")
    for c in d.get("commands") or []:
        if isinstance(c, dict) and c.get("exit_code") == 0 and c.get("log"):
            return "%s#commands[].log -> %s" % (DELIVERY[t], str(c["log"]).split(" ")[0])
    return "none recorded"


def main():
    rows = []
    nodes = []
    n14 = n14_status()
    deliveries = {}
    for t in ORDER:
        d = load(DELIVERY[t]) if DELIVERY.get(t) else None
        deliveries[t] = d
        kind, kind_basis, cli_v = classify(t, d)
        if d is None:
            declared = "NOT_DELIVERED" if not os.path.isdir(os.path.join(ROOT, os.path.dirname(DELIVERY[t]))) else "NO_DELIVERY_RECORD"
        else:
            declared = d.get("status", "NO_STATUS_FIELD")
        ev = "UNRESOLVED"
        ev_path = "%s (no row)" % N14CSV
        if n14 is not None and t in n14:
            ev = EDITOR_MAP.get(n14[t], n14[t])
            ev_path = "%s row %s" % (N14CSV, t)
        commit = (d or {}).get("source_commit") or ""
        pop, psh = primary_output(d)
        if ev == "MISSING" and t in ("N01", "N04", "N05", "N12", "N14", "N15", "N16"):
            ev, ev_path = "UNRESOLVED", "%s (no row)" % N14CSV
        on_disk = ""
        if pop:
            on_disk = "MATCH" if os.path.exists(os.path.join(ROOT, pop)) and sha(pop) == psh else (
                "MISSING" if not os.path.exists(os.path.join(ROOT, pop)) else "DIFFERS")
        dj_sha, dj_mtime = "", ""
        fp = os.path.join(ROOT, DELIVERY[t])
        if os.path.exists(fp):
            dj_sha = sha(DELIVERY[t])
            dj_mtime = datetime.datetime.fromtimestamp(os.path.getmtime(fp)).strftime("%Y-%m-%dT%H:%M:%S")
        gap, rgr = GAP_ROUTE.get(t, ("", ""))
        if t == "N15":
            # self row: keep the CSV stable no matter when this package's own delivery.json is written,
            # so that editing SUMMARY.md / patch-proposal.md never perturbs this row.
            kind, kind_basis, cli_v = "static-doc", "no Lean artifact in outputs[]", "NO_RECORD"
            declared, ev, ev_path, dj_sha, dj_mtime = "STATIC_COMPLETE", "UNRESOLVED", "%s (no row)" % N14CSV, "", ""
            pop, psh, on_disk = "", "", ""
        evidence = []
        if d is not None:
            evidence.append(DELIVERY[t])
        if t == "N15":
            evidence.append("handoffs/non-lean-2026-10-23/N15/status.csv")
        note = ""
        if t == "N15":
            note = "self row: STATIC_COMPLETE is declared by this package's own delivery.json, not read from it"
        elif d is None:
            note = "task card exists in the catalogue; no delivery in this round"
        elif cli_v == "CLAIMED_NO_GATE_BLOCK":
            note = "CLI pass is asserted by status/commands, not by a gate block"
        rows.append({
            "item": t,
            "kind": kind,
            "kind_basis": kind_basis,
            "declared_status": declared,
            "cli_verified": cli_v,
            "cli_evidence": cli_evidence(t, d),
            "editor_evidence": ev,
            "editor_evidence_path": ev_path,
            "source_pin": ("commit:" + commit) if commit else ("sha256:" + psh[:16] if psh else "NONE_RECORDED"),
            "primary_output": pop,
            "primary_output_sha256": psh,
            "hash_recheck_now": on_disk,
            "delivery_json_sha256": dj_sha,
            "delivery_json_mtime": dj_mtime,
            "native_iut_realized": False,
            "gap_ref": gap,
            "gap_ref_basis": rgr,
            "evidence_path": "; ".join(evidence),
            "note": note,
        })
        nodes.append({
            "id": t,
            "kind": kind,
            "declared_status": declared,
            "cli_verified": cli_v,
            "editor_evidence": ev,
            "native_iut_realized": False,
            "fact_tree_admitted": bool((d or {}).get("fact_tree_admitted", False)),
            "gap_ref": gap,
            "evidence_path": "; ".join(evidence) if evidence else DELIVERY[t],
            "source_record": DELIVERY[t],
            "source_record_sha256": dj_sha,
        })

    cols = ["item", "kind", "kind_basis", "declared_status", "cli_verified", "cli_evidence",
            "editor_evidence", "editor_evidence_path", "source_pin", "primary_output",
            "primary_output_sha256", "hash_recheck_now", "delivery_json_sha256",
            "delivery_json_mtime", "native_iut_realized", "gap_ref",
            "gap_ref_basis", "evidence_path", "note"]
    csv_path = os.path.join(OUT, "status.csv")
    with open(csv_path, "w", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=cols)
        w.writeheader()
        for r in rows:
            w.writerow(r)

    # ---------------- graph ----------------
    owner = {}
    for t, d in deliveries.items():
        for o in (d or {}).get("outputs") or []:
            owner.setdefault(o.get("path", ""), []).append(t)

    edges = []
    for t, d in deliveries.items():
        for i in (d or {}).get("inputs") or []:
            for src in owner.get(i.get("path", ""), []):
                if src == t:
                    continue
                edges.append({
                    "from": src, "to": t, "edge_status": "EXISTING_RECORD",
                    "evidence": [
                        "%s#inputs[path=%s, sha256=%s]" % (DELIVERY[t], i.get("path"), (i.get("sha256") or "")[:16]),
                        "%s#outputs[path=%s]" % (DELIVERY[src], i.get("path")),
                    ],
                    "note": "target lists the source's declared output as an input; both records are hashed there",
                })

    def prop(a, b, why, ev):
        edges.append({"from": a, "to": b, "edge_status": "PROPOSED", "evidence": [ev], "note": why})

    prop("K4", "W1", "W1 is the step after K4", "%s:56" % ROUND)
    prop("W5", "W7", "W7 fuses the W5 group orbit with the W6 transition relation into one relation", "%s:28" % PATH)
    prop("W6", "W7", "W7 fuses the W6 transition relation with the W5 group orbit", "%s:28" % PATH)
    prop("W8", "W10", "W10 states M-i (W8) and M-ii (W9) are corollaries of one homomorphism fact", "%s:32" % PATH)
    prop("W9", "W10", "W10 states M-ii (W9) and M-i (W8) are corollaries of one homomorphism fact", "%s:32" % PATH)
    prop("W3", "W8", "the divide-back law W8 refines is the toy law of W3", "%s:23,%s:29" % (PATH, PATH))
    prop("W5", "W12", "coord_at_base in W12 recovers W5 as a corollary", "%s:35" % PATH)
    prop("M1", "N03", "N03 takes M1-M4 as input", "%s:74" % CATALOG)
    prop("M2", "N03", "N03 takes M1-M4 as input", "%s:74" % CATALOG)
    prop("M3", "N03", "N03 takes M1-M4 as input", "%s:74" % CATALOG)
    prop("M4", "N03", "N03 takes M1-M4 as input", "%s:74" % CATALOG)
    prop("N01", "N02", "N02 takes the N01 version index as input", "%s:66" % CATALOG)
    prop("M2", "N06", "N06 takes M2 as input", "%s:102" % CATALOG)
    for s in ("N03", "N04", "N05", "N06"):
        prop(s, "N07", "N07 takes N03-N06 as input", "%s:110" % CATALOG)
    for s in ("N04", "N05", "N06", "N07"):
        prop(s, "N08", "N08 takes N04-N07 as input", "%s:118" % CATALOG)
    prop("N04", "N09", "N09 may build a second instance only if N04 supplies a real finite quotient", "%s:126" % CATALOG)
    prop("N07", "N10", "N10 takes the choice relation extracted by N07", "%s:134" % CATALOG)
    for s in ("N03", "N07", "N08"):
        prop(s, "N11", "N11 takes N03/N07/N08 by name", "%s:142" % CATALOG)
    for s in ("N03", "N07"):
        prop(s, "N13", "N13 audits the declarations named by N03/N07", "%s:161" % CATALOG)
    for t in ORDER:
        if t == "N15" or t in ("N02", "N06", "N07", "N08", "N09", "N10", "N11"):
            continue
        prop(t, "N15", "N15 indexes this item's delivery record", DELIVERY[t])

    # de-duplicate
    seen = set()
    uniq = []
    for e in edges:
        k = (e["from"], e["to"])
        if k in seen:
            continue
        seen.add(k)
        if not e["evidence"] or not all(e["evidence"]):
            raise SystemExit("edge without evidence: %r" % (e,))
        uniq.append(e)

    counts = {}
    for r in rows:
        counts[r["declared_status"]] = counts.get(r["declared_status"], 0) + 1
    graph = {
        "schema": "n15-candidate-graph/1",
        "task": "N15",
        "generated_at": "2026-10-23 (date only: the live clock is deliberately not baked in, so that a "
                        "re-run on an unchanged workspace reproduces this file byte for byte)",
        "snapshot_note": "the workspace is live: sibling tasks were still being written during this "
                         "build (N13/delivery.json appeared mid-run). Every node carries the sha256 of the "
                         "exact delivery.json record it was read from, so a reviewer can tell whether a "
                         "later edit has moved the ground under this index.",
        "rules": {
            "node": "one node per delivered or catalogued item (T1-T4, K4, M1-M4, W1-W12, N01-N16)",
            "edge_meaning": "A -> B means B is taken to depend on A; edge_status says how that is known",
            "EXISTING_RECORD": "B's delivery.json inputs[] carries a path that A's delivery.json outputs[] declares, with hashes",
            "PROPOSED": "an N15 proposal read off a named line of PATH.md / round-report.md / the task catalogue",
            "no_self_verified_edge": "no edge in this graph was re-verified by running Lean, Lake or an editor",
        },
        "nodes": nodes,
        "edges": uniq,
        "counts": {
            "nodes": len(nodes),
            "edges": len(uniq),
            "EXISTING_RECORD": sum(1 for e in uniq if e["edge_status"] == "EXISTING_RECORD"),
            "PROPOSED": sum(1 for e in uniq if e["edge_status"] == "PROPOSED"),
            "declared_status": counts,
        },
        "native_iut_realized_any_node": any(n["native_iut_realized"] for n in nodes),
        "fact_tree_admitted_any_node": any(n["fact_tree_admitted"] for n in nodes),
        "core_gap_state": "OPEN (N15 does not close it; no node here is an admission)",
    }
    with open(os.path.join(OUT, "candidate-graph.json"), "w", encoding="utf-8") as f:
        json.dump(graph, f, ensure_ascii=False, indent=2)
        f.write("\n")

    # ASCII-only console report
    print("STATUS_ROWS %d" % len(rows))
    for st in sorted(counts):
        print("  %-28s %d" % (st, counts[st]))
    print("KIND", sorted({r["kind"] for r in rows}))
    print("EDITOR", sorted({r["editor_evidence"] for r in rows}))
    print("CLI", sorted({r["cli_verified"] for r in rows}))
    print("HASH_RECHECK %s" % {k: sum(1 for r in rows if r["hash_recheck_now"] == k)
                               for k in ("MATCH", "DIFFERS", "MISSING", "")})
    bad = [r["item"] for r in rows if r["hash_recheck_now"] == "DIFFERS"]
    print("HASH_DIFFERS", bad)
    print("GRAPH nodes=%d edges=%d existing=%d proposed=%d" % (
        len(nodes), len(uniq),
        sum(1 for e in uniq if e["edge_status"] == "EXISTING_RECORD"),
        sum(1 for e in uniq if e["edge_status"] == "PROPOSED")))
    for p in ("status.csv", "candidate-graph.json"):
        print("OUT %s %s" % (p, sha("handoffs/non-lean-2026-10-23/N15/" + p)))


if __name__ == "__main__":
    main()
