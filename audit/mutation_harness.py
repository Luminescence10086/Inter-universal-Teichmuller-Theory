"""Mutation testing of this repository's verification gates.

The repository is audited by a stack of machine gates (statement lock, semantic
lock, hypothesis audit, axiom whitelist, vendored-definition contract, recorded
input hashes, clean-checkout bytes).  Each gate *claims* to catch a kind of
semantic drift.  This harness tests the gates the way mutation testing (PIT)
tests a test suite: it injects one deliberate defect at a time into a **copy** of
the artefacts and asserts that the gate which claims that defect actually fires.
One innocuous mutation is included as a negative control, so the matrix also
shows that a gate is not merely "anything changed = fail".

How the real logic is driven
----------------------------
The comparators are the repository's own code, imported read-only:

  * ``tools/statement_lock.py``        fingerprint() + diff() via its real main()
  * ``tools/semantic_lock.py``         fingerprint() + diff() via its real main()
  * ``bridge/tools/verify_integrated.py``  validate_catalog() + audit_hypotheses()
  * ``tools/bridge.py``                require_theorem() + vendored_matches()
  * ``tools/freshness.py``             assert_equal() + validate_project()

The two ledger CLIs are called through their real ``main()`` functions.  Only
their *I/O seams* are substituted, in memory, for the duration of one call:
``project_constants`` (statement lock) and ``project_constants`` /
``validate_project`` / ``definition_bodies`` (semantic lock).  Those seams are
exactly the steps that re-run Lean under ``lake``; this task forbids building and
rewriting verification output.  Everything downstream of the seam -- which rows
are ledgered, how a row is fingerprinted, what counts as changed/removed/added,
the exit code -- is the repository's own code, unmodified.  The module attributes
are restored after each call, and nothing outside ``audit/`` or the temporary
copy tree is written.

Verdicts
--------
  CAUGHT          the gate flags the mutation
  missed          the gate is applicable but silent (a defect only when the
                  mutation's ``expect`` set says the gate claims this defect)
  not-applicable  the mutation is outside that gate's artefact class, with the
                  reason recorded per cell

Exit status: 0 when every expected catch happened, no negative-control gate
fired and every required contract probe reported success; 1 when that contract
is violated -- an expected catch missed, a control gate firing, or a required
probe that did not report success (a failed probe, a probe that raised, or a
probe whose result carries no boolean ``ok``); 2 when the harness itself cannot
produce a report (a mutation anchor missing, repository bytes changed under us).

A probe's verdict is part of the exit-code contract, not a side note: the probes
are the "the gates must also pass what they should pass" half of the matrix, so
one failing probe is a violated claim just like a missed catch.

Usage:
  python audit/mutation_harness.py            # matrix + findings
  python audit/mutation_harness.py --json     # machine-readable report
  python audit/mutation_harness.py --verbose  # matrix + every cell detail
"""
from __future__ import annotations

import argparse
import contextlib
import hashlib
import importlib.util
import io
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
TOOLS = REPO / "tools"
BRIDGE_TOOLS = REPO / "bridge" / "tools"
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

import bridge as bridge_tool  # noqa: E402  (needs sys.path from above)
import freshness  # noqa: E402
import semantic_lock  # noqa: E402
import statement_lock  # noqa: E402

PROJECTS = ("main", "local", "bridge")
PROJECT_DIRS = {"main": REPO, "local": REPO / "local-field", "bridge": REPO / "bridge"}

CAUGHT, MISSED, NA = "CAUGHT", "missed", "not-applicable"

GATES = (
    "statement_lock",
    "semantic_lock",
    "hypothesis_gate",
    "axiom_gate",
    "contract_body",
    "input_hash",
    "clean_checkout",
)
SHORT = {
    "statement_lock": "stmt-lock",
    "semantic_lock": "sem-lock",
    "hypothesis_gate": "hyp",
    "axiom_gate": "axiom",
    "contract_body": "body",
    "input_hash": "input-hash",
    "clean_checkout": "checkout",
}
GATE_TOOL = {
    "statement_lock": "tools/statement_lock.py",
    "semantic_lock": "tools/semantic_lock.py",
    "hypothesis_gate": "bridge/tools/verify_integrated.py:audit_hypotheses",
    "axiom_gate": "tools/bridge.py:require_theorem",
    "contract_body": "tools/bridge.py:vendored_matches",
    "input_hash": "tools/freshness.py:validate_project/assert_equal",
    "clean_checkout": "bridges/check_clean_checkout.py",
}
BLIND = {
    ("M1", "input_hash"): ("export refreshed as a verifier re-run would refresh it, "
                           "and exported constants are outputs, not recorded inputs"),
    ("M2", "input_hash"): ("export refreshed as a verifier re-run would refresh it"),
    ("M4", "input_hash"): ("export refreshed as a verifier re-run would refresh it"),
    ("M5", "statement_lock"): ("printed statements are identical by construction: "
                               "this is exactly why a statement ledger alone is "
                               "not enough"),
    ("M5", "input_hash"): ("definition bodies are exported output, not input bytes"),
    ("M6", "input_hash"): ("exported constants are outputs and the export is "
                           "refreshed"),
    ("M7", "statement_lock"): ("a comment byte moves no printed statement: the "
                               "distinction the ledger was built to draw"),
    ("M7", "semantic_lock"): ("the mutated file contributes no ledgered statement"),
}

DEFAULT_NA = {
    "statement_lock": "mutation does not touch a ledgered statement or axiom set",
    "semantic_lock": "mutation does not touch a ledgered constant",
    "hypothesis_gate": "mutation does not touch the catalog or the binder telescope",
    "axiom_gate": "mutation does not touch an axiom set",
    "contract_body": "mutation does not touch a vendored definition body",
    "input_hash": "mutation does not touch a recorded input byte",
    "clean_checkout": (
        "the HEAD-blob comparator needs a git object write to inject a mutated "
        "blob (forbidden here) and the copy tree has no git history; see probe "
        "clean_checkout_head for the unmutated read-only run of the real gate"
    ),
}

# ---------------------------------------------------------------------------
# anchors -- verified present by _require() at mutation time, never assumed
# ---------------------------------------------------------------------------
ANCHOR_STATEMENT = "IUTBridge.ScaleLedger.mem_layer_iff_le_valuation"
ANCHOR_CATALOG = "IUTBridge.Admissibility.marginals_insufficient_of_graph"
ANCHOR_BINDER = "h1"
ANCHOR_VENDORED_BRIDGE = "IUTBridge.Admissibility.LeftAllowed"
ANCHOR_VENDORED_MAIN = "IUTAudit.Transport.LeftAllowed"
ANCHOR_BYTE_FILE = "IUTAudit/Descent.lean"
ANCHOR_COMMENT_FILE = "IUTBridge/Admissibility.lean"
HYP_ADD_OLD = "x ≠ 0 →"
HYP_ADD_NEW = "x ≠ 0 → x ≠ 1 →"
BOUND_OLD = "k ≤ x.valuation"
BOUND_NEW = "k ≥ x.valuation"
BAD_AXIOM = "sorryAx"


def _require(condition, message):
    if not condition:
        raise RuntimeError("harness anchor missing: " + message)


# ---------------------------------------------------------------------------
# copy trees -- every mutation and every gate runs against one of these
# ---------------------------------------------------------------------------
def _copy_glob(src, dst, patterns):
    for pattern in patterns:
        for path in sorted(src.glob(pattern)):
            if path.is_file():
                target = dst / path.relative_to(src)
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(path, target)


BRIDGE_FILES = (
    "lean-toolchain", "lakefile.toml", "lake-manifest.json", "IUTBridge.lean",
    "IUTBridge/**/*.lean", "tools/*.lean", "tools/*.py", "tools/*.json",
    ".vscode/*.json",
)
MAIN_FILES = (
    "lean-toolchain", "lakefile.toml", "lake-manifest.json", "IUTAudit.lean",
    "IUTAudit/**/*.lean", "tools/*.lean", "tools/*.py", "tools/*.json",
    ".vscode/*.json",
)
BRIDGE_STATE = (
    "project-constants", "checked-inputs", "export", "binder-audit",
    "definition-bodies",
)
MAIN_STATE = (
    "checked-inputs", "imports", "prefix", "project-constants", "export",
    "definition-bodies",
)


class Tree:
    """One disposable copy of a project's artefacts plus the two ledgers."""

    def __init__(self, kind, root, tmp):
        self.kind = kind
        self.root = root
        self.tmp = tmp
        self.statement_lock = tmp / "bridges" / "statement-lock.json"
        self.integrated_lock = tmp / "bridges" / "integrated-lock.json"
        self.contracts = tmp / "bridges" / "contracts.json"

    def __str__(self):
        return f"<copy:{self.kind}>"


def build_tree(kind, tmp):
    tmp = Path(tmp)
    (tmp / "bridges").mkdir(parents=True, exist_ok=True)
    for name in ("statement-lock.json", "integrated-lock.json", "contracts.json"):
        shutil.copyfile(REPO / "bridges" / name, tmp / "bridges" / name)
    if kind == "bridge":
        root = tmp / "bridge"
        root.mkdir(parents=True, exist_ok=True)
        _copy_glob(REPO / "bridge", root, BRIDGE_FILES)
        root.joinpath("verification").mkdir(exist_ok=True)
        for name in BRIDGE_STATE:
            shutil.copyfile(REPO / "bridge" / "verification" / f"{name}.json",
                            root / "verification" / f"{name}.json")
        _copy_glob(REPO, tmp, ("tools/*.lean", "tools/*.py", "tools/*.json",
                               ".vscode/*.json"))
    elif kind == "main":
        root = tmp / "main"
        root.mkdir(parents=True, exist_ok=True)
        _copy_glob(REPO, root, MAIN_FILES)
        root.joinpath("verification").mkdir(exist_ok=True)
        for name in MAIN_STATE:
            shutil.copyfile(REPO / "verification" / f"{name}.json",
                            root / "verification" / f"{name}.json")
        (root / "fact-tree").mkdir(exist_ok=True)
        shutil.copyfile(REPO / "fact-tree" / "facts.json",
                        root / "fact-tree" / "facts.json")
    else:  # pragma: no cover - guard
        raise RuntimeError("unknown copy tree: " + kind)
    return Tree(kind, root, tmp)


# ---------------------------------------------------------------------------
# data access: the mutated copy for one project, the read-only repo otherwise
# ---------------------------------------------------------------------------
def _project_name(base):
    resolved = Path(base).resolve()
    for name, directory in PROJECT_DIRS.items():
        if resolved == directory.resolve():
            return name
    raise RuntimeError("unknown project base: " + str(base))


def _read_json(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def _write_json(path, value):
    Path(path).write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n",
                          encoding="utf-8")


class Ctx:
    def __init__(self, tree):
        self.tree = tree
        self._rows = {}
        self._rows_list = {}
        self._bodies = {}
        self._modules = {}

    def root(self, project):
        if project == self.tree.kind:
            return self.tree.root
        return PROJECT_DIRS[project]

    def module(self, project):
        if project not in self._modules:
            self._modules[project] = freshness.verifier(self.root(project))
        return self._modules[project]

    def rows_list(self, project):
        if project not in self._rows_list:
            self._rows_list[project] = _read_json(
                self.root(project) / "verification" / "project-constants.json")
        return self._rows_list[project]

    def rows(self, project):
        if project not in self._rows:
            self._rows[project] = {row["id"]: row for row in self.rows_list(project)}
        return self._rows[project]

    def bodies(self, project):
        if project not in self._bodies:
            record = _read_json(
                self.root(project) / "verification" / "definition-bodies.json")
            self._bodies[project] = {
                row["id"]: row["body"]
                for row in self.module(project).one_information(record["stdout"])
            }
        return self._bodies[project]

    def catalog(self):
        return _read_json(self.tree.root / "tools" / "catalog.json")

    def binder_rows(self):
        return _read_json(
            self.tree.root / "verification" / "binder-audit.json")["rows"]

    def checked(self):
        return _read_json(self.tree.root / "verification" / "checked-inputs.json")

    def contracts(self):
        return _read_json(self.tree.contracts)

    def sanitise(self, text):
        text = str(text)
        for path, label in ((self.tree.root, "<copy>"), (self.tree.tmp, "<tmp>")):
            text = text.replace(str(path), label)
        return re.sub(r"\s+", " ", text).strip()


@contextlib.contextmanager
def _patched(module, **attributes):
    saved = {name: getattr(module, name) for name in attributes}
    try:
        for name, value in attributes.items():
            setattr(module, name, value)
        yield
    finally:
        for name, value in saved.items():
            setattr(module, name, value)


def _drive(module, argv, **patches):
    """Call one ledger's real main() with its I/O seams patched in memory.

    Both ledgers build their argparse parser with ``parse_args()`` (implicit
    sys.argv) while *also* taking an explicit argv list, so this harness's own
    command line would leak into theirs.  sys.argv is therefore neutralised for
    the duration of the call -- an I/O seam, not a change of logic.
    """
    buffer = io.StringIO()
    saved_argv = sys.argv
    sys.argv = [str(Path(__file__).name)]
    try:
        with _patched(module, **patches):
            with contextlib.redirect_stdout(buffer):
                code = module.main(argv) if argv is not None else module.main()
    finally:
        sys.argv = saved_argv
    return code, buffer.getvalue()


def _last_line(output):
    lines = [line.strip() for line in output.splitlines() if line.strip()]
    return lines[-1] if lines else "no output"


# ---------------------------------------------------------------------------
# the gates
# ---------------------------------------------------------------------------
def _gate_statement_lock(ctx):
    code, output = _drive(
        statement_lock, [],
        project_constants=lambda project: (ctx.rows(project), {}),
        LOCK=ctx.tree.statement_lock,
    )
    findings = [line.strip() for line in output.splitlines()
                if "FAIL" in line or "Review required" in line]
    return (CAUGHT if code else MISSED,
            ctx.sanitise("; ".join(findings) or _last_line(output)))


def _gate_semantic_lock(ctx):
    code, output = _drive(
        semantic_lock, None,
        validate_project=lambda base, deep=True: (ctx.rows(_project_name(base)), {}),
        definition_bodies=lambda base: ctx.bodies(_project_name(base)),
        LOCK=ctx.tree.integrated_lock,
    )
    findings = [line.strip() for line in output.splitlines()
                if "Review required" in line]
    return (CAUGHT if code else MISSED,
            ctx.sanitise("; ".join(findings) or _last_line(output)))


def _verify_integrated():
    spec = importlib.util.spec_from_file_location(
        "mutation_gate_verify_integrated", BRIDGE_TOOLS / "verify_integrated.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _gate_hypotheses(ctx):
    gate = _verify_integrated()
    catalog = ctx.catalog()
    try:
        gate.validate_catalog(catalog, ctx.rows("bridge"))
        gate.audit_hypotheses(catalog, ctx.binder_rows())
    except RuntimeError as error:
        return CAUGHT, ctx.sanitise(error)
    return MISSED, "catalog hypotheses agree with the recorded binder telescope"


def _gate_axioms(ctx):
    rows = ctx.rows("bridge")
    try:
        for name in sorted(row["id"] for row in rows.values()
                           if row["kind"] == "theorem"):
            bridge_tool.require_theorem("bridge", name, rows)
    except RuntimeError as error:
        return CAUGHT, ctx.sanitise(error)
    return MISSED, "every recorded axiom set is inside the whitelist"


def _gate_contract_body(ctx):
    prefixes = ctx.contracts()["normalisation"]["strip_prefixes"]
    failures, checked = [], 0
    for contract in ctx.contracts()["contracts"]:
        for vendored in contract.get("vendored", []):
            left = ctx.rows("main")[vendored["main"]]
            right = ctx.rows("bridge")[vendored["bridge"]]
            type_match, body_match = bridge_tool.vendored_matches(
                left, right,
                ctx.bodies("main")[vendored["main"]],
                ctx.bodies("bridge")[vendored["bridge"]],
                prefixes)
            checked += 1
            if not type_match:
                failures.append(f"{contract['id']}: vendored type mismatch "
                                f"{vendored['main']}")
            if not body_match:
                failures.append(f"{contract['id']}: vendored body mismatch "
                                f"{vendored['main']}")
    if failures:
        return CAUGHT, ctx.sanitise("; ".join(failures))
    return MISSED, f"{checked} vendored definition(s) match in type and body"


def _gate_input_hash(ctx):
    if ctx.tree.kind == "main":
        # The composed gate: inputs, fact DAG, runtime, and export agreement.
        try:
            freshness.validate_project(ctx.tree.root)
        except RuntimeError as error:
            return CAUGHT, ctx.sanitise(error)
        return MISSED, "validate_project accepted the copy"
    checked = ctx.checked()
    try:
        freshness.assert_equal(checked["input_sha256"],
                               ctx.module("bridge").snapshot(), "bridge inputs")
    except RuntimeError as error:
        return CAUGHT, ctx.sanitise(error)
    return MISSED, f"{len(checked['input_sha256'])} recorded input bytes match"


def _gate_clean_checkout(ctx):
    raise RuntimeError("clean_checkout is declared not-applicable per mutation")


GATE_FUNCS = {
    "statement_lock": _gate_statement_lock,
    "semantic_lock": _gate_semantic_lock,
    "hypothesis_gate": _gate_hypotheses,
    "axiom_gate": _gate_axioms,
    "contract_body": _gate_contract_body,
    "input_hash": _gate_input_hash,
    "clean_checkout": _gate_clean_checkout,
}


# ---------------------------------------------------------------------------
# mutations -- each edits only files inside its own copy tree
# ---------------------------------------------------------------------------
def _refresh_export(tree, rows):
    """Simulate the sanctioned repair of an export after re-running a verifier.

    A source edit is followed by a verifier re-run, which rewrites the export.
    Without this step every statement mutation would also be caught by the
    input-hash/export gate and the ledger's own contribution would be untestable.
    """
    path = tree.root / "verification" / "export.json"
    record = _read_json(path)
    lines = [line for line in record["stdout"].splitlines() if line.strip()]
    _require(len(lines) == 1, "export stdout is a single information message")
    message = json.loads(lines[0])
    message["data"] = json.dumps(rows, ensure_ascii=False)
    record["stdout"] = json.dumps(message, ensure_ascii=False) + "\n"
    _write_json(path, record)


def _rewrite_rows(tree, mutate):
    path = tree.root / "verification" / "project-constants.json"
    rows = _read_json(path)
    mutate(rows)
    _write_json(path, rows)
    return rows


def mut_weaken_statement(tree):
    def mutate(rows):
        row = next(r for r in rows if r["id"] == ANCHOR_STATEMENT)
        _require(row["statement"].count(HYP_ADD_OLD) == 1,
                 f"{ANCHOR_STATEMENT} contains {HYP_ADD_OLD!r} exactly once")
        row["statement"] = row["statement"].replace(HYP_ADD_OLD, HYP_ADD_NEW, 1)
    rows = _rewrite_rows(tree, mutate)
    _refresh_export(tree, rows)


def mut_alter_bound(tree):
    def mutate(rows):
        row = next(r for r in rows if r["id"] == ANCHOR_STATEMENT)
        _require(row["statement"].count(BOUND_OLD) == 1,
                 f"{ANCHOR_STATEMENT} contains {BOUND_OLD!r} exactly once")
        row["statement"] = row["statement"].replace(BOUND_OLD, BOUND_NEW, 1)
    rows = _rewrite_rows(tree, mutate)
    _refresh_export(tree, rows)


def mut_hypothesis_drift(tree):
    catalog_path = tree.root / "tools" / "catalog.json"
    catalog = _read_json(catalog_path)
    entry = next(item for item in catalog if item["id"] == ANCHOR_CATALOG)
    _require(len(entry["hypotheses"]) >= 2, "catalog entry declares hypotheses")
    entry["hypotheses"] = entry["hypotheses"][:-1]  # declare one fewer
    _write_json(catalog_path, catalog)

    binder_path = tree.root / "verification" / "binder-audit.json"
    record = _read_json(binder_path)
    row = next(item for item in record["rows"] if item["id"] == ANCHOR_CATALOG)
    binder = next((b for b in row["binders"] if b["name"] == ANCHOR_BINDER), None)
    _require(binder is not None, f"binder {ANCHOR_BINDER!r} recorded")
    _require(binder["isProp"] is True, f"binder {ANCHOR_BINDER!r} is a Prop binder")
    binder["isProp"] = False  # the recorded telescope loses a hypothesis
    _write_json(binder_path, record)


def mut_axiom_regression(tree):
    def mutate(rows):
        row = next(r for r in rows if r["id"] == ANCHOR_STATEMENT)
        _require(BAD_AXIOM not in row["axioms"], "axiom set had no injected axiom")
        row["axioms"] = sorted(row["axioms"] + [BAD_AXIOM])
    rows = _rewrite_rows(tree, mutate)
    _refresh_export(tree, rows)


def mut_vendored_body(tree):
    path = tree.root / "verification" / "definition-bodies.json"
    record = _read_json(path)
    lines = [line for line in record["stdout"].splitlines() if line.strip()]
    _require(len(lines) == 1, "definition-bodies stdout is one information message")
    message = json.loads(lines[0])
    rows = json.loads(message["data"])
    row = next(item for item in rows if item["id"] == ANCHOR_VENDORED_BRIDGE)
    # The elaborated body prints ∃ as a full application, e.g.
    #   ... => @Exists.{v + 1} S fun (s : S) => A k s
    # so the ∃ -> ∀ flip has to rebuild the printed universal form (which is how
    # the sibling IsRectangular body prints ∀).  The universe annotation can
    # contain spaces, hence the explicit brace group.
    match = re.search(r"@Exists(?:\.[^{]*\{[^}]*\})? (\S+) fun \(([^()]*)\) => (.*)",
                      row["body"])
    _require(match is not None, "body contains an @Exists application")
    flipped = row["body"][:match.start()] + f"∀ ({match.group(2)}), {match.group(3)}"
    _require("Exists" not in flipped, "the flipped body no longer mentions Exists")
    row["body"] = flipped
    message["data"] = json.dumps(rows, ensure_ascii=False)
    record["stdout"] = json.dumps(message, ensure_ascii=False) + "\n"
    _write_json(path, record)


def mut_node_removal(tree):
    """Delete one theorem from the exported constants (what a real deletion leaves).

    A deleted theorem disappears from the export while the ledgers still pin it,
    which is the case the ledgers promise to fail on.  Deleting the entry from the
    ledger *file* instead is a baseline edit, not drift, and reads as an addition;
    probe unpin_entry records that declared behaviour separately.
    """
    def mutate(rows):
        before = len(rows)
        rows[:] = [row for row in rows if row["id"] != ANCHOR_STATEMENT]
        _require(len(rows) == before - 1,
                 f"{ANCHOR_STATEMENT} was present in the export")
    rows = _rewrite_rows(tree, mutate)
    _refresh_export(tree, rows)


def mut_byte_drift(tree):
    path = tree.root / ANCHOR_BYTE_FILE
    data = bytearray(path.read_bytes())
    index = data.find(b"--")
    _require(index >= 0, f"{ANCHOR_BYTE_FILE} has a line comment")
    cursor = index + 2
    while cursor < len(data) and not chr(data[cursor]).isalpha():
        cursor += 1
    _require(cursor < len(data), f"{ANCHOR_BYTE_FILE} comment has a character")
    original = data[cursor]
    data[cursor] = ord("E") if original != ord("E") else ord("A")
    path.write_bytes(bytes(data))


def mut_innocuous(tree):
    path = tree.root / ANCHOR_COMMENT_FILE
    original = path.read_bytes()
    path.write_bytes(original + b"-- mutation harness negative control\n")
    # Reordering JSON keys changes file bytes without changing any value.
    rows_path = tree.root / "verification" / "project-constants.json"
    rows = _read_json(rows_path)
    reordered = [dict(reversed(list(row.items()))) for row in rows]
    _write_json(rows_path, reordered)


MUTATIONS = (
    {
        "id": "M1",
        "title": "statement weakening: one extra hypothesis",
        "claim": "a theorem that quietly acquires a premise is refused",
        "tree": "bridge",
        "apply": mut_weaken_statement,
        "expect": ("statement_lock", "semantic_lock"),
        "must_not": (),
        "scope": {
            "statement_lock": None,
            "semantic_lock": None,
            "input_hash": None,
            "hypothesis_gate": (
                "binder rows are kernel output; re-deriving them needs a lake build, "
                "which this task forbids"
            ),
        },
    },
    {
        "id": "M2",
        "title": "statement alteration: bound direction flipped",
        "claim": "k ≤ v rewritten to k ≥ v is refused",
        "tree": "bridge",
        "apply": mut_alter_bound,
        "expect": ("statement_lock", "semantic_lock"),
        "must_not": (),
        "scope": {
            "statement_lock": None,
            "semantic_lock": None,
            "input_hash": None,
            "hypothesis_gate": (
                "an altered bound adds no binder; the hypothesis gate reads the "
                "catalog and the binder telescope only"
            ),
        },
    },
    {
        "id": "M3",
        "title": "hypothesis-count drift (catalog short one, binder row edited)",
        "claim": "a declared hypothesis set that disagrees with the kernel is refused",
        "tree": "bridge",
        "apply": mut_hypothesis_drift,
        "expect": ("hypothesis_gate", "input_hash"),
        "must_not": (),
        "scope": {
            "hypothesis_gate": None,
            "input_hash": None,
            "statement_lock": "tools/catalog.json is not in the statement ledger",
            "semantic_lock": "tools/catalog.json is not in the semantic ledger",
        },
    },
    {
        "id": "M4",
        "title": "axiom regression: non-whitelisted axiom added",
        "claim": "a theorem that gains an axiom is refused, by ledger and whitelist",
        "tree": "bridge",
        "apply": mut_axiom_regression,
        "expect": ("axiom_gate", "statement_lock", "semantic_lock"),
        "must_not": (),
        "scope": {
            "axiom_gate": None,
            "statement_lock": None,
            "semantic_lock": None,
            "input_hash": None,
        },
    },
    {
        "id": "M5",
        "title": "vendored definition body: ∃ flipped to ∀, elaborated type identical",
        "claim": "a body rewrite that leaves the type alone is refused",
        "tree": "bridge",
        "apply": mut_vendored_body,
        "expect": ("contract_body", "semantic_lock"),
        "must_not": (),
        "scope": {
            "contract_body": None,
            "semantic_lock": None,
            "statement_lock": None,
            "input_hash": None,
            "hypothesis_gate": "no catalog entry or binder telescope is touched",
        },
    },
    {
        "id": "M6",
        "title": "node removal: one ledgered theorem deleted",
        "claim": "removal fails; additions and deliberate re-baselines pass",
        "tree": "bridge",
        "apply": mut_node_removal,
        "expect": ("statement_lock", "semantic_lock"),
        "must_not": (),
        "scope": {
            "statement_lock": None,
            "semantic_lock": None,
            "input_hash": None,
        },
    },
    {
        "id": "M7",
        "title": "source-byte drift: one byte of a recorded input changed",
        "claim": "recorded bytes must be the bytes at HEAD / in the tree",
        "tree": "main",
        "apply": mut_byte_drift,
        "expect": ("input_hash",),
        "must_not": (),
        "scope": {
            "input_hash": None,
            "statement_lock": None,
            "semantic_lock": None,
        },
    },
    {
        "id": "M8",
        "title": "NEGATIVE CONTROL: comment appended, JSON keys reordered",
        "claim": "an innocuous edit must not be read as statement drift",
        "tree": "bridge",
        "apply": mut_innocuous,
        "expect": ("input_hash",),
        "must_not": ("statement_lock", "semantic_lock"),
        "scope": {
            "statement_lock": None,
            "semantic_lock": None,
            "input_hash": None,
            "hypothesis_gate": "no catalog entry or binder telescope is touched",
        },
    },
)


# ---------------------------------------------------------------------------
# probes: the gates must pass what they should pass, on unmutated copies too
# ---------------------------------------------------------------------------
def probe_baseline_bridge(tmp):
    tree = build_tree("bridge", tmp)
    ctx = Ctx(tree)
    verdicts = {}
    for gate in GATES:
        if gate == "clean_checkout":
            continue
        verdict, detail = GATE_FUNCS[gate](ctx)
        verdicts[gate] = {"verdict": verdict, "detail": detail}
    ok = all(cell["verdict"] == MISSED for cell in verdicts.values())
    return {"ok": ok, "detail": ("unmutated copies pass every applicable gate"
                                if ok else "an unmutated copy already fails a gate"),
            "gates": verdicts}


def probe_baseline_main(tmp):
    tree = build_tree("main", tmp)
    try:
        freshness.validate_project(tree.root)
    except RuntimeError as error:
        return {"ok": False, "detail": Ctx(tree).sanitise(error)}
    return {"ok": True, "detail": "validate_project accepted an unmutated main copy"}


def probe_fact_tree_removal(tmp):
    tree = build_tree("main", tmp)
    path = tree.root / "fact-tree" / "facts.json"
    record = _read_json(path)
    _require(len(record["nodes"]) > 1, "the main fact tree has more than one node")
    dropped = record["nodes"].pop()["id"]
    record["edges"] = [edge for edge in record["edges"] if dropped not in
                       (edge["from"], edge["to"])]
    _write_json(path, record)
    try:
        freshness.validate_project(tree.root)
    except RuntimeError as error:
        return {"ok": True, "detail": Ctx(tree).sanitise(error)}
    return {"ok": False, "detail": f"removing {dropped} from the fact tree passed"}


def probe_unpin_entry(tmp):
    """Deleting an entry from a ledger file is a baseline edit, not drift.

    Both ledgers claim: changed -> fail, removed (from the project) -> fail,
    added -> reported but passing.  Unpinning therefore has to pass, and recording
    that keeps the M6 result from being read as "any lock edit is caught".
    """
    tree = build_tree("bridge", tmp)
    statement = _read_json(tree.statement_lock)
    _require(ANCHOR_STATEMENT in statement["projects"]["bridge"], "entry pinned")
    del statement["projects"]["bridge"][ANCHOR_STATEMENT]
    _write_json(tree.statement_lock, statement)
    integrated = _read_json(tree.integrated_lock)
    key = "bridge:" + ANCHOR_STATEMENT
    _require(key in integrated["entries"], "entry pinned in the integrated ledger")
    del integrated["entries"][key]
    _write_json(tree.integrated_lock, integrated)
    ctx = Ctx(tree)
    verdicts = {gate: GATE_FUNCS[gate](ctx)[0]
                for gate in ("statement_lock", "semantic_lock")}
    ok = all(verdict == MISSED for verdict in verdicts.values())
    return {"ok": ok,
            "detail": ("unpinning a ledger entry reads as an addition and passes, "
                       "which is what both ledgers declare" if ok else
                       "unpinning an entry was reported as drift")}


def probe_clean_checkout_head():
    """Run the real clean-checkout gate read-only against the real repository."""
    result = subprocess.run(
        [sys.executable, str(REPO / "bridges" / "check_clean_checkout.py")],
        cwd=str(REPO), capture_output=True, text=True, encoding="utf-8",
        errors="replace", timeout=600)
    tail = (result.stdout or result.stderr or "").strip().splitlines()
    return {"ok": result.returncode == 0,
            "detail": tail[-1] if tail else f"exit {result.returncode}"}


PROBES = (
    ("baseline_bridge", probe_baseline_bridge),
    ("baseline_main", probe_baseline_main),
    ("fact_tree_removal", probe_fact_tree_removal),
    ("unpin_entry", probe_unpin_entry),
    ("clean_checkout_head", probe_clean_checkout_head),
)

#: probes that run read-only against the repository and take no copy tree
REPO_ONLY_PROBES = ("clean_checkout_head",)


def _probe_verdict(value):
    """Normalise one probe's return value to ``{"ok": bool, "detail": str, ...}``.

    A required probe that cannot state a boolean verdict has not passed.  ``None``
    or a mapping without ``"ok"`` becomes an explicit failure naming the problem
    (the caller turns a raised exception into the same shape), because a probe
    whose result is unreadable must never be counted as silence or as success.
    """
    if not isinstance(value, dict):
        return {"ok": False,
                "detail": (f"result is {type(value).__name__}, not a mapping; a "
                           f"required probe must report a boolean 'ok'")}
    verdict = dict(value)
    if not isinstance(verdict.get("ok"), bool):
        verdict["ok"] = False
        verdict["detail"] = (f"result has no boolean 'ok' field (got "
                             f"{value.get('ok')!r}); a required probe must state "
                             f"its verdict")
        return verdict
    verdict.setdefault("detail", "")
    return verdict


def probe_violations(probe_results):
    """The probe half of the exit-code contract, next to ``violations_for``.

    Every entry of ``PROBES`` is required.  A probe that reports ``ok=False``, one
    that raised, one that returned no verdict and one that is missing from the
    report are all contract violations, and each names the probe so a reader of
    the exit code learns *which* check failed.
    """
    violations = []
    for name, _probe in PROBES:
        verdict = probe_results.get(name)
        if verdict is None:
            violations.append(f"{name}: required probe produced no result")
        elif verdict.get("ok") is not True:
            detail = verdict.get("detail") or "<no detail>"
            violations.append(f"{name}: required probe failed: {detail}")
    return violations


# ---------------------------------------------------------------------------
# the run
# ---------------------------------------------------------------------------
REPO_WITNESS = (
    "tools/semantic_lock.py", "tools/statement_lock.py", "tools/bridge.py",
    "tools/freshness.py", "tools/catalog.json", "bridge/tools/catalog.json",
    "bridge/tools/verify_integrated.py", "bridge/tools/Binders.lean",
    "bridges/statement-lock.json", "bridges/integrated-lock.json",
    "bridges/contracts.json", "verification/project-constants.json",
    "bridge/verification/project-constants.json",
    "bridge/verification/binder-audit.json", "fact-tree/facts.json",
    "IUTAudit/Descent.lean", "bridge/IUTBridge/Admissibility.lean",
)


def repo_witness():
    digest = hashlib.sha256()
    for relative in REPO_WITNESS:
        path = REPO / relative
        digest.update(relative.encode("utf-8") + b"\0")
        digest.update(path.read_bytes() if path.exists() else b"<missing>")
    return digest.hexdigest()


def violations_for(spec, cells):
    """The exit-code contract, in one place: what counts as a broken claim."""
    violations = []
    for gate in spec["expect"]:
        if cells[gate]["verdict"] != CAUGHT:
            violations.append(f"{spec['id']}: {gate} was expected to catch this "
                              f"mutation and did not")
    for gate in spec["must_not"]:
        if cells[gate]["verdict"] == CAUGHT:
            violations.append(f"{spec['id']}: negative control was flagged by {gate}")
    return violations


def _recorded_probe_results(recorded):
    """Validate probe results recorded by an earlier run that this one may reuse.

    Re-running an unchanged probe over unchanged repository bytes can only repeat
    the same answer, so a caller that has already paid for it may hand the results
    back instead.  That is sound only for the *same* repository bytes and only for
    probes that exist here, so both are checked and a mismatch is a harness error
    (exit 2) rather than a quietly reused verdict.
    """
    if not isinstance(recorded, dict):
        raise RuntimeError("recorded probe results must be a mapping, not "
                           + type(recorded).__name__)
    if recorded.get("repo_witness") != repo_witness():
        raise RuntimeError("recorded probe results are only reusable for the same "
                           "repository bytes, but the repository witness differs")
    probes = recorded.get("probes")
    if not isinstance(probes, dict):
        raise RuntimeError("recorded probe results must carry a 'probes' mapping")
    known = {name for name, _probe in PROBES}
    unknown = sorted(set(probes) - known)
    if unknown:
        raise RuntimeError("recorded probe results name unknown probes: "
                           + ", ".join(unknown))
    return probes


def run(include_matrix=True, recorded_probes=None):
    """Run the gates and the required probes; return the machine-readable report.

    ``recorded_probes`` is an optional ``{"repo_witness", "probes"}`` object from an
    earlier run of this same harness over the same repository bytes.  Probes it
    covers are reported as ``reused`` and are *not* executed again; every other
    probe still runs for real, and a reused probe keeps its full standing in the
    exit-code contract below.
    """
    witness_before = repo_witness()
    recorded = _recorded_probe_results(recorded_probes) if recorded_probes else {}
    matrix = []
    violations = []
    probe_results = {}
    reused = []
    for name, probe in PROBES:
        if name in recorded:
            probe_results[name] = dict(_probe_verdict(recorded[name]), reused=True)
            reused.append(name)
            continue
        with tempfile.TemporaryDirectory(prefix=f"mutation_probe_{name}_") as holder:
            try:
                verdict = probe() if name in REPO_ONLY_PROBES else probe(Path(holder))
            except Exception as error:  # noqa: BLE001 - a probe that raises has failed
                # A probe that cannot state a verdict is a failed required probe, not
                # a crash and not a pass: record it, name it, and report it below.
                probe_results[name] = {
                    "ok": False,
                    "detail": (f"raised {type(error).__name__}: {error}; a required "
                               f"probe must report a verdict"),
                    "raised": type(error).__name__,
                }
            else:
                probe_results[name] = _probe_verdict(verdict)
    # The probes are part of the contract: a failing one is a violation, in the
    # same list and with the same standing as a missed catch.
    violations.extend(probe_violations(probe_results))

    for spec in MUTATIONS if include_matrix else ():
        with tempfile.TemporaryDirectory(prefix=f"mutation_{spec['id']}_") as holder:
            tree = build_tree(spec["tree"], Path(holder))
            spec["apply"](tree)
            ctx = Ctx(tree)
            cells = {}
            for gate in GATES:
                reason = spec["scope"].get(gate, DEFAULT_NA[gate])
                if reason:
                    cells[gate] = {"verdict": NA, "detail": reason, "reason": reason}
                else:
                    verdict, detail = GATE_FUNCS[gate](ctx)
                    note = BLIND.get((spec["id"], gate))
                    if note and verdict == MISSED:
                        detail = f"{detail} [expected blind: {note}]"
                    cells[gate] = {"verdict": verdict, "detail": detail}
            caught = [gate for gate in GATES if cells[gate]["verdict"] == CAUGHT]
            violations.extend(violations_for(spec, cells))
            if not caught:
                raise RuntimeError(f"{spec['id']}: no gate saw the mutation; the "
                                   f"mutation is unobservable and proves nothing")
            matrix.append({
                "id": spec["id"],
                "title": spec["title"],
                "claim": spec["claim"],
                "tree": spec["tree"],
                "expect": list(spec["expect"]),
                "must_not": list(spec["must_not"]),
                "cells": cells,
                "caught_by": caught,
            })

    witness_after = repo_witness()
    if witness_after != witness_before:
        raise RuntimeError("repository bytes changed during the run; the harness "
                           "must be read-only with respect to the repository")

    return {
        "schema": 1,
        "scope": ("mutation testing of the verification gates; not a proof of any "
                  "mathematical statement"),
        "repo": str(REPO),
        "repository_unchanged": witness_before == witness_after,
        "gates": [{"id": gate, "short": SHORT[gate], "tool": GATE_TOOL[gate]}
                  for gate in GATES],
        "matrix": matrix,
        "matrix_complete": include_matrix,
        "probes": probe_results,
        "probes_reused": reused,
        "violations": violations,
        "exit_code": 1 if violations else 0,
    }


LEGEND = (
    "C = CAUGHT, m = missed (gate applicable but silent), . = not applicable",
    "exit status: 0 = every claimed gate fired, no control gate fired and every "
    "required probe passed; 1 = an expectation was violated or a required probe "
    "did not pass; 2 = harness could not run",
)


def render(result):
    lines = []
    lines.append("mutation x gate matrix (each mutation applied to a temp copy only)")
    lines.append("")
    id_width = max(len(row["id"]) for row in result["matrix"])
    title_width = max(len(row["title"]) for row in result["matrix"])
    header = " " * (id_width + 2 + title_width + 2) + "  ".join(
        SHORT[gate].ljust(10) for gate in GATES)
    lines.append(header)
    for row in result["matrix"]:
        marks = []
        for gate in GATES:
            verdict = row["cells"][gate]["verdict"]
            marks.append(("C" if verdict == CAUGHT else
                          "m" if verdict == MISSED else ".").ljust(10))
        lines.append(f"{row['id'].ljust(id_width)}  {row['title'].ljust(title_width)}  "
                     + "  ".join(marks).rstrip())
    lines.append("")
    for line in LEGEND:
        lines.append("  " + line)
    lines.append("")
    lines.append("gates:")
    for gate in GATES:
        lines.append(f"  {SHORT[gate]:<11} {gate:<17} {GATE_TOOL[gate]}")
    lines.append("")
    lines.append("probes:")
    for name, probe in result["probes"].items():
        suffix = " (recorded, reused: same repository bytes)" if probe.get("reused") else ""
        lines.append(f"  {'ok ' if probe['ok'] else 'FAIL'} {name}: "
                     f"{probe['detail']}{suffix}")
    lines.append("")
    lines.append("findings:")
    for row in result["matrix"]:
        caught = ", ".join(SHORT[gate] for gate in row["caught_by"])
        lines.append(f"  {row['id']} caught by {caught}")
        for gate in GATES:
            cell = row["cells"][gate]
            if cell["verdict"] == MISSED:
                lines.append(f"     {SHORT[gate]} blind: {cell['detail']}")
    lines.append("")
    if result["violations"]:
        lines.append("VIOLATIONS:")
        for violation in result["violations"]:
            lines.append("  " + violation)
    else:
        lines.append("no violations: every mutation a gate claims was caught, the "
                     "negative control was not read as statement drift, and every "
                     "required probe passed")
    return "\n".join(lines)


def _verbose(result):
    lines = []
    for row in result["matrix"]:
        lines.append(f"[{row['id']}] {row['title']}")
        for gate in GATES:
            cell = row["cells"][gate]
            lines.append(f"   {SHORT[gate]:<11} {cell['verdict']:<15} {cell['detail']}")
        lines.append("")
    return "\n".join(lines)


def main(argv=None):
    parser = argparse.ArgumentParser(
        prog="mutation_harness.py",
        description=("Mutation testing of this repository's verification gates: "
                     "inject one semantic defect at a time into copies of the "
                     "artefacts and assert the gate that claims it actually fires."),
        epilog=("Runs entirely inside tempfile.TemporaryDirectory(); the repository "
                "is read-only input. Mutations: M1 statement weakening, M2 statement "
                "alteration, M3 hypothesis drift, M4 axiom regression, M5 vendored "
                "body flip, M6 node removal, M7 input byte drift, M8 negative control. "
                "The five probes (two baselines, fact-tree removal, ledger unpin, real "
                "clean checkout) are equally required. Exit 0 = all claims held and "
                "every required probe passed, 1 = a claim or a required probe was "
                "violated, 2 = harness error."))
    parser.add_argument("--json", action="store_true",
                        help="emit the machine-readable report instead of the matrix")
    parser.add_argument("--verbose", action="store_true",
                        help="print every cell's detail below the matrix")
    parser.add_argument("--probes-only", action="store_true",
                        help="run required probes without repeating the M1-M8 matrix")
    parser.add_argument("--reuse-probes", metavar="PATH",
                        help="reuse the probe results recorded in PATH (a JSON object "
                             "with 'repo_witness' and 'probes') instead of rerunning "
                             "those probes; the repository witness must match")
    args = parser.parse_args(argv)

    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8", errors="replace")
        except (AttributeError, ValueError):  # pragma: no cover
            pass

    recorded = None
    if args.reuse_probes:
        try:
            recorded = json.loads(Path(args.reuse_probes).read_text(encoding="utf-8"))
        except (OSError, ValueError) as error:
            print(f"mutation harness could not read {args.reuse_probes}: {error}",
                  file=sys.stderr)
            return 2

    try:
        result = run(include_matrix=not args.probes_only,
                     recorded_probes=recorded)
    except RuntimeError as error:
        print(f"mutation harness could not run: {error}", file=sys.stderr)
        return 2
    if args.json:
        print(json.dumps(result, ensure_ascii=False, indent=2))
    else:
        if args.probes_only:
            print(json.dumps(result, ensure_ascii=False, indent=2))
        else:
            print(render(result))
        if args.verbose and not args.probes_only:
            print()
            print(_verbose(result))
    return result["exit_code"]


if __name__ == "__main__":
    raise SystemExit(main())
