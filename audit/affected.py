#!/usr/bin/env python3
"""audit/affected.py -- incremental review scoping for this verification repository.

In this repository the expensive build step is not a compile: it is the human/editor
observation recorded in ``verification/vscode-receipt.json`` (a schema-3 receipt for
``bridge``).  This tool imports the "affected targets" idea from incremental build
systems (Bazel, CI path filters) and applies it to that observation step: given a
commit range, the staged index, or an explicit file list, report exactly which
recorded evidence is invalidated and what has to be redone.

Per changed file the tool classifies, from the *recorded* data only:

  project-input    the path is a key of some project's ``input_sha256`` (Lean sources,
                   toolchain files, lakefile/manifest, ``tools/*``) or of the schema-3
                   ``dependency_sha256`` (cross-project), or it is the receipt's own
                   ``evidence`` file.  Any of these voids that project's receipt, so
                   every admitted node of that project returns to pending.
  theorem-source   a fact-tree node's ``source`` changed; the node and everything that
                   transitively depends on it (``depends_on`` / ``edges``) must be
                   re-verified *and* re-observed.
  contract-record  ``bridges/contracts.json`` or ``bridges/facts.json`` changed, or a
                   contract endpoint (abstract / concrete / vendored) lives in a
                   changed file or an invalidated node, or an endpoint's project lost
                   its admission -> that contract must be re-audited.
  semantic-lock    ``bridges/statement-lock.json`` / ``integrated-lock.json`` changed.
  documentation    markdown/text/research notes: no machine evidence is invalidated.
  unpinned         a code/config change that no receipt pins (it still may rewrite
                   evidence by hand -- the reviewer has to read it).

The tool is read-only: it never writes, never runs lake, never runs a verifier and
never touches ``tools/``, ``*.lean`` or ``verification/`` output.  It only reads
recorded JSON and runs read-only git (``diff``, ``log``).

What the recorded keys cannot answer is *membership*: the real verifiers glob their input
sets (``IUTBridge/**/*.lean``, ``tools/*.py``, ``.vscode/*.json``), so a file that appears
after the observation changes the input map while appearing in no recorded key.  Rather
than re-implementing those patterns here -- they would drift from
``bridge/tools/verify_integrated.py`` / ``tools/verify.py`` the moment either file is
edited -- the tool imports each project's own production snapshot function and asks one
question per changed path: *is this path a live member of that project's input set?*  A
member that no recorded key covers means the observation no longer spans the input set,
so the receipt is VOID.  Where the snapshot cannot be computed (missing verifier, deleted
hard-coded input, unavailable source checkout) the receipt is UNKNOWN -- never INTACT.

Usage
-----
  python audit/affected.py --range 78bc059..HEAD
  python audit/affected.py --range b8f2566..
  python audit/affected.py --files bridge/IUTBridge/Admissibility.lean
  python audit/affected.py --staged --json
  python audit/affected.py --range HEAD~1..HEAD --json > affected.json

Exit status: 0 = analysis produced (whatever it found), 1 = the analysis itself
failed (missing records, bad revision, no git), 2 = command-line misuse.
"""

from __future__ import annotations

import argparse
import importlib.util
import inspect
import json
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

TOOL = "audit/affected.py"

WORKSPACE_PREFIX = "@workspace/"
CONTRACT_RECORDS = ("bridges/contracts.json", "bridges/facts.json")
SEMANTIC_LOCK_FILES = ("bridges/statement-lock.json", "bridges/integrated-lock.json")

#: Suffixes that are prose, not machine-checked evidence.
DOC_SUFFIXES = (".md", ".txt", ".rst", ".pdf", ".log", ".tex", ".csv")
#: Directories whose contents are research/review prose or captured sources.
DOC_DIRS = ("research/", "reviews/")

#: Depth-1 directories that are never projects or are handled separately.
SKIP_DIRS = {
    ".git", ".lake", ".vscode", "audit", "bridges", "fact-tree",
    "research", "reviews", "tools", "verification",
}

CLASS_ORDER = (
    "outside-repo",
    "project-input",
    "theorem-source",
    "contract-record",
    "semantic-lock",
    "documentation",
    "unpinned",
)

#: Long lists are elided in the human summary; ``--json`` always carries them in full.
HUMAN_ROW_LIMIT = 20


class ToolError(RuntimeError):
    """A condition that prevents the analysis (not a finding)."""


# --------------------------------------------------------------------------------------
# small helpers
# --------------------------------------------------------------------------------------
def norm_path(value: str) -> str:
    """Normalise a repository-relative path to POSIX form without a './' prefix."""
    text = str(value).replace("\\", "/")
    while text.startswith("./"):
        text = text[2:]
    return text.strip("/") if text not in ("/", "") else text


def load_json(path: Path, *, required: bool) -> object | None:
    try:
        with path.open("r", encoding="utf-8") as handle:
            return json.load(handle)
    except FileNotFoundError:
        if required:
            raise ToolError(f"missing record: {path}")
        return None
    except OSError as exc:
        raise ToolError(f"cannot read {path}: {exc}") from exc
    except json.JSONDecodeError as exc:
        raise ToolError(f"unreadable JSON in {path}: {exc}") from exc


def anchor_to_root(key: str, root_name: str, project_rels: tuple[str, ...] = ()) -> str | None:
    """Map a recorded absolute path back to a repository-relative path.

    Schema 3 records some dependency pins as absolute paths.  Anchoring on the last
    occurrence of the repository directory name keeps ``.../local-field/tools/verify.py``
    from being mistaken for the repository's own ``tools/verify.py``.

    A receipt recorded in one checkout is also read in another (a git worktree, a copy),
    where the repository directory name differs while the project directories do not.
    In that case anchor on the longest known project directory instead, so the pin is
    still recognised rather than silently lost.
    """
    segments = key.replace("\\", "/").split("/")
    if root_name in segments:
        index = len(segments) - 1 - segments[::-1].index(root_name)
        tail = "/".join(segments[index + 1:])
        return tail or None
    best: str | None = None
    for rel in sorted(project_rels, key=lambda item: (-len(item), item)):
        rel_segments = rel.split("/")
        width = len(rel_segments)
        for index in range(len(segments) - width, -1, -1):
            if segments[index:index + width] == rel_segments:
                candidate = "/".join(segments[index:])
                if best is None or len(candidate) > len(best):
                    best = candidate
                break
    return best


def _strings(value) -> list[str]:
    if isinstance(value, str):
        return [value]
    if isinstance(value, (list, tuple)):
        out: list[str] = []
        for item in value:
            out.extend(_strings(item))
        return out
    return []


# --------------------------------------------------------------------------------------
# git (read-only)
# --------------------------------------------------------------------------------------
def git(root: Path, *args: str, check: bool = True) -> str:
    cmd = ["git", "-C", str(root), "-c", "core.quotepath=false", *args]
    try:
        proc = subprocess.run(
            cmd, capture_output=True, text=True, encoding="utf-8", errors="replace"
        )
    except FileNotFoundError as exc:  # pragma: no cover - environment dependent
        raise ToolError("git executable not found on PATH") from exc
    if proc.returncode != 0:
        if check:
            lines = (proc.stderr or proc.stdout).strip().splitlines()
            detail = lines[-1] if lines else "unknown git error"
            raise ToolError(f"git {' '.join(args)} failed: {detail}")
        return ""
    return proc.stdout


def git_toplevel(root: Path) -> Path | None:
    try:
        out = git(root, "rev-parse", "--show-toplevel", check=False).strip()
    except ToolError:  # pragma: no cover - git missing
        return None
    return Path(out) if out else None


@dataclass(frozen=True)
class Change:
    path: str
    status: str


def _parse_name_status(text: str, root: Path, toplevel: Path) -> list[Change]:
    changes: list[Change] = []

    def locate(raw: str) -> str | None:
        absolute = (toplevel / raw).resolve()
        try:
            return absolute.relative_to(root).as_posix()
        except ValueError:
            return None  # outside the repository

    for line in text.splitlines():
        if not line.strip():
            continue
        parts = line.split("\t")
        status = parts[0].strip()[:1] or "?"
        if status in ("R", "C") and len(parts) >= 3:
            for raw in (parts[1], parts[2]):
                located = locate(raw)
                changes.append(Change(located if located else norm_path(raw), status))
            continue
        if len(parts) >= 2:
            located = locate(parts[1])
            changes.append(Change(located if located else norm_path(parts[1]), status))
    return changes


def changes_from_range(root: Path, toplevel: Path, spec: str) -> tuple[list[Change], list[dict]]:
    if "..." in spec:
        left = spec.split("...", 1)[0]
        for rev in (left or "HEAD",):
            if not git(root, "rev-parse", "--verify", f"{rev}^{{commit}}", check=False).strip():
                raise ToolError(f"unknown revision in range: {rev!r}")
        diff = git(root, "diff", "--name-status", "-M", "--no-ext-diff", spec)
        log = git(root, "log", "--format=%h%x09%s", spec)
    else:
        if ".." in spec:
            left, right = spec.split("..", 1)
            left = left or "HEAD"
            right = right or "HEAD"
        else:
            left, right = spec, "HEAD"
        for rev in (left, right):
            if not git(root, "rev-parse", "--verify", f"{rev}^{{commit}}", check=False).strip():
                raise ToolError(f"unknown revision: {rev!r}")
        diff = git(root, "diff", "--name-status", "-M", "--no-ext-diff", left, right)
        log = git(root, "log", "--format=%h%x09%s", f"{left}..{right}")
    commits = []
    for line in log.splitlines():
        if not line.strip():
            continue
        sha, _, subject = line.partition("\t")
        commits.append({"sha": sha.strip(), "subject": subject.strip()})
    return _parse_name_status(diff, root, toplevel), commits


def changes_from_staged(root: Path, toplevel: Path) -> list[Change]:
    diff = git(root, "diff", "--cached", "--name-status", "-M", "--no-ext-diff")
    return _parse_name_status(diff, root, toplevel)


def changes_from_files(root: Path, toplevel: Path, raw_paths: list[str]) -> list[Change]:
    changes: list[Change] = []
    cwd = Path.cwd()
    for raw in raw_paths:
        candidate = Path(raw)
        if candidate.is_absolute():
            try:
                rel = candidate.resolve().relative_to(root).as_posix()
            except ValueError:
                changes.append(Change(norm_path(raw), "?"))
                continue
            changes.append(Change(rel, "="))
            continue
        repo_relative = norm_path(raw)
        if (root / repo_relative).exists():
            changes.append(Change(repo_relative, "="))
            continue
        from_cwd = (cwd / raw).resolve()
        try:
            rel = from_cwd.relative_to(root).as_posix()
        except ValueError:
            rel = None
        if rel and from_cwd.exists():
            changes.append(Change(rel, "="))
        else:
            changes.append(Change(repo_relative, "="))  # deleted or future file
    return changes


# --------------------------------------------------------------------------------------
# recorded state
# --------------------------------------------------------------------------------------
@dataclass
class Node:
    id: str
    module: str
    source: str
    status: str
    depends_on: tuple[str, ...] = ()


@dataclass
class Project:
    name: str
    rel: str  # '' for the repository-root project, else e.g. 'local-field'
    inputs: dict[str, str]
    dependencies: dict[str, str]
    evidence: str | None
    receipt_schema: int | None
    checked_targets: tuple[str, ...]
    nodes: dict[str, Node]
    dependents: dict[str, tuple[str, ...]]
    catalog: dict[str, str]
    modules: dict[str, str] = field(default_factory=dict)
    root_name: str = ""
    sibling_rels: tuple[str, ...] = ()
    warnings: list[str] = field(default_factory=list)

    # -- paths -------------------------------------------------------------------
    def repo_path(self, project_relative: str) -> str:
        return project_relative if not self.rel else f"{self.rel}/{project_relative}"

    def project_relative(self, repo_relative: str) -> str | None:
        if not self.rel:
            return repo_relative
        prefix = f"{self.rel}/"
        return repo_relative[len(prefix):] if repo_relative.startswith(prefix) else None

    # -- lookup ------------------------------------------------------------------
    def source_of(self, name: str) -> str | None:
        """Best-effort project-relative source file for a fully qualified Lean name."""
        if name in self.catalog:
            return self.catalog[name]
        node = self.nodes.get(name)
        if node is not None and node.source:
            return node.source
        best: tuple[int, str] | None = None
        for module, source in self.modules.items():
            if name == module or name.startswith(module + "."):
                if best is None or len(module) > best[0]:
                    best = (len(module), source)
        return best[1] if best else None

    def closure(self, seeds) -> set[str]:
        """Transitive dependents of ``seeds`` (excluding the seeds themselves)."""
        seen = set(seeds)
        stack = list(seeds)
        while stack:
            current = stack.pop()
            for dependent in self.dependents.get(current, ()):  # deterministic tuple
                if dependent not in seen:
                    seen.add(dependent)
                    stack.append(dependent)
        return seen - set(seeds)

    def pins_for(self, repo_relative: str) -> list[tuple[str, str]]:
        """Recorded keys this path satisfies: list of (key, kind)."""
        found: list[tuple[str, str]] = []
        relative = self.project_relative(repo_relative)
        if relative is not None and relative != "":
            if relative in self.inputs:
                found.append((relative, "input"))
            if relative in self.dependencies:
                found.append((relative, "dependency"))
        workspace_key = WORKSPACE_PREFIX + repo_relative
        if workspace_key in self.inputs:
            found.append((workspace_key, "input"))
        if workspace_key in self.dependencies:
            found.append((workspace_key, "dependency"))
        # Absolute dependency keys (schema 3 records them as absolute paths).
        for key in self.dependencies:
            if not isinstance(key, str) or key == relative or key in self.inputs:
                continue
            if anchor_to_root(key, self.root_name, self.sibling_rels) == repo_relative:
                found.append((key, "dependency"))
        if self.evidence and self.repo_path(self.evidence) == repo_relative:
            found.append((self.evidence, "evidence"))
        return found


def _has_records(directory: Path) -> bool:
    return any(
        (directory / candidate).is_file()
        for candidate in (
            "verification/checked-inputs.json",
            "verification/vscode-receipt.json",
            "fact-tree/facts.json",
            "tools/catalog.json",
        )
    )


def discover_projects(root: Path) -> dict[str, str]:
    """Map project name -> project path relative to the repository root."""
    mapping: dict[str, str] = {}
    recorded = load_json(root / "bridges/facts.json", required=False)
    if isinstance(recorded, dict) and isinstance(recorded.get("projects"), dict):
        for name, rel in sorted(recorded["projects"].items()):
            if not isinstance(name, str) or not isinstance(rel, str):
                continue
            path = root / rel
            if path.is_dir() and _has_records(path):
                mapping[name] = "" if norm_path(rel) == "." else norm_path(rel)
    try:
        entries = sorted(p for p in root.iterdir() if p.is_dir())
    except OSError as exc:
        raise ToolError(f"cannot list {root}: {exc}") from exc
    for entry in entries:
        if entry.name.startswith(".") or entry.name in SKIP_DIRS:
            continue
        if not _has_records(entry):
            continue
        if entry.name in mapping.values():
            continue
        mapping.setdefault(entry.name, entry.name)
    if _has_records(root):
        mapping.setdefault("main", "")
    if not mapping:
        raise ToolError(
            f"no verification records found under {root} "
            "(expected */verification/checked-inputs.json or */fact-tree/facts.json)"
        )
    return {name: mapping[name] for name in sorted(mapping)}


def _endpoint_items(value) -> list[tuple[str | None, str]]:
    """Flatten an endpoint field into (project, name) pairs."""
    out: list[tuple[str | None, str]] = []
    if value is None:
        return out
    if isinstance(value, str):
        if value.strip():
            out.append((None, value.strip()))
        return out
    if isinstance(value, dict):
        if isinstance(value.get("theorem"), str):
            project = value.get("project")
            out.append((project if isinstance(project, str) else None, value["theorem"]))
            return out
        for key, item in value.items():
            if not isinstance(item, str):
                continue
            if key in ("theorem", "project"):
                continue
            out.append((key, item))
        return out
    if isinstance(value, (list, tuple)):
        for item in value:
            out.extend(_endpoint_items(item))
    return out


@dataclass
class Contract:
    id: str
    kind: str | None
    status: str | None
    sources: list[str]
    endpoints: list[tuple[str, str | None, str]]  # (role, project, name)


@dataclass
class Records:
    root: Path
    projects: dict[str, Project]
    contracts: list[Contract]
    lock_modules: dict[str, str]  # 'project:Name' -> module
    lock_kinds: dict[str, str]
    statement_counts: dict[str, int]
    warnings: list[str]

    # -- construction --------------------------------------------------------------
    @classmethod
    def load(cls, root: Path) -> "Records":
        root = root.resolve()
        warnings: list[str] = []
        projects: dict[str, Project] = {}
        for name, rel in discover_projects(root).items():
            projects[name] = _load_project(root, name, rel, warnings)
        # Absolute dependency pins may have been recorded in another checkout of this
        # same workspace; anchoring needs the sibling project directories.
        rels = tuple(sorted({project.rel for project in projects.values() if project.rel}))
        for project in projects.values():
            project.sibling_rels = rels
        contracts = _load_contracts(root, warnings)
        lock_modules, lock_kinds = _load_integrated_lock(root, warnings)
        statement_counts = _load_statement_counts(root, warnings, lock_modules)
        return cls(
            root=root,
            projects=projects,
            contracts=contracts,
            lock_modules=lock_modules,
            lock_kinds=lock_kinds,
            statement_counts=statement_counts,
            warnings=warnings,
        )

    # -- lookup --------------------------------------------------------------------
    def project_by_alias(self, alias: str | None) -> str | None:
        if not alias:
            return None
        if alias in self.projects:
            return alias
        lowered = alias.lower()
        for name, project in self.projects.items():
            if name.lower() == lowered:
                return name
            if project.rel and (project.rel == alias or project.rel.split("/")[-1] == alias):
                return name
        return None

    def resolve_endpoint(self, project_hint: str | None, name: str) -> tuple[str | None, str | None]:
        """(project name, source path relative to the project) for a Lean name."""
        order: list[str] = []
        hinted = self.project_by_alias(project_hint)
        if hinted:
            order.append(hinted)
        order.extend(sorted(n for n in self.projects if n not in order))
        for project_name in order:
            project = self.projects[project_name]
            lock_module = self.lock_modules.get(f"{project_name}:{name}")
            if lock_module:
                source = project.modules.get(lock_module)
                if source:
                    return project_name, source
            source = project.source_of(name)
            if source:
                return project_name, source
        return None, None


def _load_project(root: Path, name: str, rel: str, warnings: list[str]) -> Project:
    base = root / rel if rel else root
    label = rel or "."

    checked = load_json(base / "verification/checked-inputs.json", required=False)
    receipt = load_json(base / "verification/vscode-receipt.json", required=False)
    if not isinstance(checked, dict) and not isinstance(receipt, dict):
        raise ToolError(f"project {name!r}: no checked-inputs.json or vscode-receipt.json under {base}")

    inputs: dict[str, str] = {}
    dependencies: dict[str, str] = {}
    for source_name, record in (("checked-inputs.json", checked), ("vscode-receipt.json", receipt)):
        if not isinstance(record, dict):
            continue
        for field_name, target in (("input_sha256", inputs), ("dependency_sha256", dependencies)):
            block = record.get(field_name)
            if isinstance(block, dict):
                for key, value in block.items():
                    if isinstance(key, str) and isinstance(value, str):
                        if key in target and target[key] != value:
                            warnings.append(
                                f"{label}: {field_name}[{key}] differs between recorded files "
                                f"({source_name} disagrees with earlier record); both hashes are stale"
                            )
                        target.setdefault(key, value)

    evidence = receipt.get("evidence") if isinstance(receipt, dict) else None
    if not isinstance(evidence, str):
        evidence = None
    schema = None
    for record in (receipt, checked):
        if isinstance(record, dict) and isinstance(record.get("schema"), int):
            schema = record["schema"]
            break
    targets = ()
    for record in (checked, receipt):
        if isinstance(record, dict) and isinstance(record.get("checked_targets"), list):
            targets = tuple(_strings(record["checked_targets"]))
            break

    nodes: dict[str, Node] = {}
    dependents: dict[str, set[str]] = {}
    modules: dict[str, str] = {}
    facts = load_json(base / "fact-tree/facts.json", required=False)
    if isinstance(facts, dict) and isinstance(facts.get("nodes"), list):
        for row in facts["nodes"]:
            if not isinstance(row, dict) or not isinstance(row.get("id"), str):
                continue
            node_id = row["id"]
            source = row.get("source") if isinstance(row.get("source"), str) else ""
            module = row.get("module") if isinstance(row.get("module"), str) else ""
            if not module:
                module = node_id.rsplit(".", 1)[0] if "." in node_id else node_id
            depends = tuple(sorted(_strings(row.get("depends_on"))))
            nodes[node_id] = Node(
                id=node_id,
                module=module,
                source=norm_path(source) if source else "",
                status=str(row.get("status") or "unknown"),
                depends_on=depends,
            )
            if source:
                modules.setdefault(module, norm_path(source))
        for row in facts.get("edges") or []:
            if not isinstance(row, dict):
                continue
            head, tail = row.get("from"), row.get("to")
            if isinstance(head, str) and isinstance(tail, str):
                dependents.setdefault(head, set()).add(tail)
        for node in nodes.values():
            for dependency in node.depends_on:
                dependents.setdefault(dependency, set()).add(node.id)

    catalog: dict[str, str] = {}
    raw_catalog = load_json(base / "tools/catalog.json", required=False)
    if isinstance(raw_catalog, dict):
        raw_catalog = raw_catalog.get("theorems") or raw_catalog.get("entries") or []
    if isinstance(raw_catalog, list):
        for row in raw_catalog:
            if not isinstance(row, dict):
                continue
            theorem = row.get("id")
            source = row.get("source")
            if isinstance(theorem, str) and isinstance(source, str):
                catalog[theorem] = norm_path(source)
                modules.setdefault(theorem.rsplit(".", 1)[0] if "." in theorem else theorem,
                                   norm_path(source))

    if not nodes and targets:
        # No fact-tree: fall back to the receipt's admitted target list.
        for theorem in targets:
            source = catalog.get(theorem, "")
            nodes[theorem] = Node(id=theorem, module="", source=source, status="admitted")
        if nodes:
            warnings.append(f"{label}: fact-tree/facts.json missing; node set taken from receipt targets")

    return Project(
        name=name,
        rel=rel,
        inputs=dict(sorted(inputs.items())),
        dependencies=dict(sorted(dependencies.items())),
        evidence=evidence,
        receipt_schema=schema,
        checked_targets=targets,
        nodes=dict(sorted(nodes.items())),
        dependents={key: tuple(sorted(value)) for key, value in sorted(dependents.items())},
        catalog=dict(sorted(catalog.items())),
        modules=dict(sorted(modules.items())),
        root_name=root.name,
        warnings=[],
    )


def _load_contracts(root: Path, warnings: list[str]) -> list[Contract]:
    merged: dict[str, Contract] = {}
    for rel in CONTRACT_RECORDS:
        data = load_json(root / rel, required=False)
        if data is None:
            continue
        rows = data.get("contracts") if isinstance(data, dict) else data
        if not isinstance(rows, list):
            warnings.append(f"{rel}: no 'contracts' list found")
            continue
        for row in rows:
            if not isinstance(row, dict):
                continue
            cid = row.get("id")
            if not isinstance(cid, str) or not cid:
                continue
            entry = merged.get(cid)
            if entry is None:
                entry = Contract(id=cid, kind=None, status=None, sources=[], endpoints=[])
                merged[cid] = entry
            if rel not in entry.sources:
                entry.sources.append(rel)
            if entry.kind is None and isinstance(row.get("kind"), str):
                entry.kind = row["kind"]
            if isinstance(row.get("status"), str):
                entry.status = row["status"]
            for role in ("abstract", "concrete", "vendored"):
                for project, name in _endpoint_items(row.get(role)):
                    key = (role, project, name)
                    if key not in entry.endpoints:
                        entry.endpoints.append(key)
    return [merged[cid] for cid in sorted(merged)]


def _load_integrated_lock(root: Path, warnings: list[str]) -> tuple[dict[str, str], dict[str, str]]:
    data = load_json(root / "bridges/integrated-lock.json", required=False)
    modules: dict[str, str] = {}
    kinds: dict[str, str] = {}
    if not isinstance(data, dict):
        return modules, kinds
    entries = data.get("entries")
    if not isinstance(entries, dict):
        return modules, kinds
    for key, row in entries.items():
        if not isinstance(key, str) or not isinstance(row, dict):
            continue
        module = row.get("module")
        if isinstance(module, str):
            modules.setdefault(key, module)
        kind = row.get("kind")
        if isinstance(kind, str):
            kinds.setdefault(key, kind)
    return modules, kinds


def _load_statement_counts(root: Path, warnings: list[str],
                           lock_modules: dict[str, str]) -> dict[str, int]:
    data = load_json(root / "bridges/statement-lock.json", required=False)
    counts: dict[str, int] = {}
    if isinstance(data, dict) and isinstance(data.get("projects"), dict):
        for name, block in data["projects"].items():
            if isinstance(block, dict):
                counts[str(name)] = len(block)
    if not counts:
        for key in sorted(lock_modules):
            project = key.split(":", 1)[0]
            counts[project] = counts.get(project, 0) + 1
    return dict(sorted(counts.items()))


# --------------------------------------------------------------------------------------
# live snapshot membership (decided by the production snapshot functions, not by us)
# --------------------------------------------------------------------------------------
#: Production entry points, in the order a schema-2 project tries them; a schema-3 receipt
#: prefers its integrated verifier.  These are the files that decide what an input set is.
SNAPSHOT_ENTRY_POINTS = (
    ("tools/verify_integrated.py", "project_snapshot"),
    ("tools/verify.py", "snapshot"),
    ("tools/verify_integrated.py", "snapshot"),
)
DEPENDENCY_FUNCTION = "dependency_snapshot"


@dataclass
class MemberSet:
    """One live input set, as reported by a project's own snapshot function."""

    status: str  # 'decided' | 'unavailable'
    source: str | None = None
    key_count: int = 0
    paths: frozenset[str] = frozenset()
    unmapped: tuple[str, ...] = ()
    error: str | None = None

    @property
    def decided(self) -> bool:
        return self.status == "decided"

    def as_row(self) -> dict:
        shown = list(self.unmapped[:5])
        return {
            "status": self.status,
            "source": self.source,
            "keys": self.key_count,
            "members": len(self.paths),
            "unmapped": shown,
            "unmapped_more": max(0, len(self.unmapped) - len(shown)),
            "error": self.error,
        }


@dataclass
class SnapshotProbe:
    """Everything one project's snapshot functions told us about its live input set."""

    project: str
    input: MemberSet
    dependency: MemberSet | None = None
    entry_points_tried: tuple[str, ...] = ()

    def as_row(self) -> dict:
        return {
            "input": self.input.as_row(),
            "dependency": self.dependency.as_row() if self.dependency is not None else None,
            "entry_points_tried": list(self.entry_points_tried),
        }


def _is_absolute_key(text: str) -> bool:
    if text.startswith("/"):
        return True
    head = text.split("/", 1)[0]
    return len(head) == 2 and head[1] == ":" and head[0].isalpha()


def _relative_to_root(key: str, root: Path) -> str | None:
    text = norm_path(key)
    if not _is_absolute_key(text):
        return None
    root_text = root.resolve().as_posix()
    if text == root_text:
        return None
    if text.startswith(root_text + "/"):
        return text[len(root_text) + 1:]
    try:
        return Path(text).resolve().relative_to(root.resolve()).as_posix()
    except (OSError, ValueError):
        return None


def member_path(project: Project, key: str, root: Path) -> str | None:
    """Repository-relative path of one snapshot key (None = this key is not a file path).

    The mapping mirrors the two conventions the verifiers use for keys: project-relative
    inside the project, ``@workspace/`` for the workspace root, and absolute paths for
    ``dependency_sha256``.
    """
    text = norm_path(key)
    if not text:
        return None
    if text.startswith(WORKSPACE_PREFIX):
        return norm_path(text[len(WORKSPACE_PREFIX):]) or None
    if text.startswith("@"):
        return None
    if _is_absolute_key(text):
        return _relative_to_root(text, root)
    if project.rel:
        if text == project.rel or text.startswith(project.rel + "/"):
            return text
        return f"{project.rel}/{text}"
    return text


def _load_verifier_module(path: Path, label: str):
    """Import a production verifier module for its snapshot function only."""
    spec = importlib.util.spec_from_file_location(label, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"{path.name}: not importable as a python module")
    module = importlib.util.module_from_spec(spec)
    previous = sys.dont_write_bytecode
    sys.dont_write_bytecode = True  # never leave __pycache__ in the observed tree
    try:
        spec.loader.exec_module(module)
    finally:
        sys.dont_write_bytecode = previous
    return module


def _positional_arity(function) -> int:
    try:
        parameters = list(inspect.signature(function).parameters.values())
    except (TypeError, ValueError):
        return 0
    count = 0
    for parameter in parameters:
        if parameter.kind is parameter.VAR_POSITIONAL:
            return count
        if parameter.kind in (parameter.POSITIONAL_ONLY, parameter.POSITIONAL_OR_KEYWORD):
            count += 1
    return count


def _call_snapshot(function, base: Path):
    """Call a snapshot function with its project directory when it accepts one."""
    return function(base) if _positional_arity(function) >= 1 else function()


def _member_set(project: Project, root: Path, snapshot, source: str) -> MemberSet:
    if not isinstance(snapshot, dict):
        return MemberSet(
            "unavailable", source=source,
            error=f"snapshot returned {type(snapshot).__name__}, not a mapping",
        )
    paths: set[str] = set()
    unmapped: list[str] = []
    for key in sorted(str(item) for item in snapshot):
        mapped = member_path(project, key, root)
        if mapped is None:
            unmapped.append(key)
        else:
            paths.add(mapped)
    return MemberSet(
        "decided", source=source, key_count=len(snapshot),
        paths=frozenset(paths), unmapped=tuple(unmapped),
    )


def _probe_dependency(project: Project, root: Path, module, filename: str) -> MemberSet | None:
    """Cross-project input set (schema-3 ``dependency_sha256``), when the module has one."""
    function = getattr(module, DEPENDENCY_FUNCTION, None)
    if not callable(function):
        return None
    source = f"{project.repo_path(filename)}:{DEPENDENCY_FUNCTION}"
    directory = getattr(module, "DEP", None)
    takes_argument = _positional_arity(function) >= 1
    try:
        if directory is None and takes_argument:
            return MemberSet(
                "unavailable", source=source,
                error="module exposes no DEP directory for its dependency snapshot",
            )
        snapshot = function(directory) if directory is not None and takes_argument else function()
    except Exception as exc:  # noqa: BLE001 - any failure means "we cannot decide"
        return MemberSet("unavailable", source=source, error=f"{type(exc).__name__}: {exc}")
    return _member_set(project, root, snapshot, source)


def probe_project(project: Project, root: Path) -> SnapshotProbe:
    """Ask the project's own production snapshot functions what their input set is."""
    base = root / project.rel if project.rel else root
    preferred = "tools/verify_integrated.py" if project.receipt_schema == 3 else "tools/verify.py"
    ordered = sorted(SNAPSHOT_ENTRY_POINTS, key=lambda entry: entry[0] != preferred)
    tried: list[str] = []
    for filename, function_name in ordered:
        path = base / filename
        if not path.is_file():
            continue
        label = f"{project.repo_path(filename)}:{function_name}"
        tried.append(label)
        try:
            module = _load_verifier_module(
                path, f"_affected_snapshot_{project.name}_{len(tried)}_{function_name}"
            )
        except Exception:  # noqa: BLE001 - an unimportable verifier is just undecidable
            continue
        function = getattr(module, function_name, None)
        if not callable(function):
            continue
        try:
            snapshot = _call_snapshot(function, base)
        except Exception as exc:  # noqa: BLE001 - e.g. a hard-coded input was deleted
            return SnapshotProbe(
                project.name,
                MemberSet("unavailable", source=label, error=f"{type(exc).__name__}: {exc}"),
                _probe_dependency(project, root, module, filename),
                tuple(tried),
            )
        return SnapshotProbe(
            project.name,
            _member_set(project, root, snapshot, label),
            _probe_dependency(project, root, module, filename),
            tuple(tried),
        )
    looked_for = ", ".join(f"{name}:{function}" for name, function in SNAPSHOT_ENTRY_POINTS)
    return SnapshotProbe(
        project.name,
        MemberSet(
            "unavailable",
            error=f"no production snapshot entry point under {base.as_posix()} "
                  f"(looked for {looked_for})",
        ),
        None,
        tuple(tried),
    )


# --------------------------------------------------------------------------------------
# analysis
# --------------------------------------------------------------------------------------
def analyse(records: Records, changes: list[Change], mode: dict,
            probe_membership: bool = True) -> dict:
    root = records.root
    warnings = list(records.warnings)

    status_by_path: dict[str, str] = {}
    for change in changes:
        status_by_path.setdefault(change.path, change.status)
    changed_paths = sorted(status_by_path)
    changed_set = set(changed_paths)

    # ---- 1. receipts that collapse -----------------------------------------------
    pins_by_project: dict[str, list[dict]] = {}
    for project_name, project in records.projects.items():
        for path in changed_paths:
            for key, kind in project.pins_for(path):
                pins_by_project.setdefault(project_name, []).append(
                    {"path": path, "key": key, "kind": kind}
                )

    # ---- 1b. live snapshot membership ---------------------------------------------
    # The recorded keys above are only the files that existed at observation time.  A
    # changed path that is a live member of the project's own snapshot set but appears
    # in no recorded key changes the input map without touching a pin, which is exactly
    # the case a pin-only planner reports as "intact".  Ask the production functions.
    probes: dict[str, SnapshotProbe] = {}
    if probe_membership:
        for project_name, project in records.projects.items():
            probes[project_name] = probe_project(project, root)
    member_of: dict[str, set[str]] = {}
    membership_rows: dict[str, dict] = {}
    for project_name, project in records.projects.items():
        label = project.rel or "."
        probe = probes.get(project_name)
        pinned_paths = {pin["path"] for pin in pins_by_project.get(project_name, [])}
        added: list[dict] = []
        if probe is not None:
            for path in changed_paths:
                if path in pinned_paths:
                    continue
                origin = None
                if probe.input.decided and path in probe.input.paths:
                    origin = "input"
                elif (probe.dependency is not None and probe.dependency.decided
                      and path in probe.dependency.paths):
                    origin = "dependency"
                if origin is not None:
                    added.append({"path": path, "origin": origin})
            for member_set in (probe.input, probe.dependency):
                if member_set is None or not member_set.decided:
                    continue
                for path in member_set.paths:
                    member_of.setdefault(path, set()).add(project_name)
        live_paths = set(probe.input.paths) if probe is not None and probe.input.decided else None
        recorded_paths: set[str] = set()
        recorded_unmapped: list[str] = []
        for key in project.inputs:
            mapped = member_path(project, key, root)
            if mapped is None:
                recorded_unmapped.append(key)
            else:
                recorded_paths.add(mapped)
        live_only = sorted(live_paths - recorded_paths) if live_paths is not None else []
        recorded_only = sorted(recorded_paths - live_paths) if live_paths is not None else []
        # A member this change set introduced is already reported per receipt; the warning
        # is for disagreement that exists independently of the change set.
        introduced = {item["path"] for item in added}
        drift_live_only = [path for path in live_only if path not in introduced]
        if drift_live_only or recorded_only:
            differing = (drift_live_only or recorded_only)[:4]
            more = len(drift_live_only) + len(recorded_only) - len(differing)
            warnings.append(
                f"{label}: the live input set and the recorded receipt also disagree "
                f"independently of this change set ({len(drift_live_only)} live-only, "
                f"{len(recorded_only)} recorded-only): " + ", ".join(differing)
                + (f" ... +{more} more" if more > 0 else "")
            )
        membership_rows[project_name] = {
            "added": added,
            "live_only": live_only,
            "recorded_only": recorded_only,
            "recorded_unmapped_keys": recorded_unmapped,
            "probe": probe.as_row() if probe is not None else None,
        }

    receipts = []
    for project_name, project in records.projects.items():
        pins = sorted(
            {(p["path"], p["key"], p["kind"]) for p in pins_by_project.get(project_name, [])}
        )
        admitted = [n for n in project.nodes.values() if n.status == "admitted"]
        if not admitted:
            admitted_count = len(project.checked_targets) or len(project.nodes)
        else:
            admitted_count = len(admitted)
        membership = membership_rows[project_name]
        probe_row = membership["probe"]
        undecided: list[str] = []
        if probe_row is None:
            undecided.append("snapshot membership probe disabled")
        else:
            for field in ("input", "dependency"):
                block = probe_row[field]
                if block is not None and block["status"] != "decided":
                    undecided.append(f"{field} set: {block['error']}")
        void = bool(pins) or bool(membership["added"])
        if void:
            status = "VOID"
        elif undecided:
            status = "UNKNOWN"
        else:
            status = "INTACT"
        receipts.append(
            {
                "project": project_name,
                "path": project.repo_path("verification/vscode-receipt.json"),
                "schema": project.receipt_schema,
                "status": status,
                "void": void,
                "pins": [
                    {"path": path, "key": key, "kind": kind} for path, key, kind in pins
                ],
                "admitted_at_observation": admitted_count,
                "nodes_to_pending": admitted_count if void else 0,
                "membership": membership,
                "not_intact_because": undecided,
            }
        )
    voided = {row["project"] for row in receipts if row["void"]}
    unknown = [row["project"] for row in receipts if row["status"] == "UNKNOWN"]
    membership_added = sum(len(row["membership"]["added"]) for row in receipts)

    # ---- 2. nodes: direct + transitive dependents --------------------------------
    per_project: dict[str, dict] = {}
    invalidated_ids: set[str] = set()
    direct_total = 0
    dependent_total = 0
    for project_name, project in records.projects.items():
        direct: set[str] = set()
        for node in project.nodes.values():
            if node.source and project.repo_path(node.source) in changed_set:
                direct.add(node.id)
        for theorem, source in project.catalog.items():
            if theorem not in project.nodes and source and project.repo_path(source) in changed_set:
                direct.add(theorem)
        if not direct and project_name not in voided:
            continue
        dependents = project.closure(direct) if direct else set()
        depended = {node.id: node for node in project.nodes.values()}
        rows_direct = [
            {"id": tid, "source": project.repo_path(project.catalog.get(tid) or (depended[tid].source if tid in depended else "") or "")}
            for tid in sorted(direct)
        ]
        rows_dependent = [
            {"id": tid, "source": project.repo_path(project.catalog.get(tid) or (depended[tid].source if tid in depended else "") or "")}
            for tid in sorted(dependents)
        ]
        # A collapsed receipt sends every admitted node back to pending.
        pending_ids = set()
        if project_name in voided:
            pending_ids = {
                node.id for node in project.nodes.values() if node.status == "admitted"
            } or set(project.checked_targets)
        invalidated_ids |= direct | dependents
        direct_total += len(direct)
        dependent_total += len(dependents)
        per_project[project_name] = {
            "direct": rows_direct,
            "dependents": rows_dependent,
            "direct_count": len(direct),
            "dependent_count": len(dependents),
            "admitted_to_pending": sorted(pending_ids) if pending_ids else [],
            "receipt_void": project_name in voided,
        }

    # ---- 3. contracts ------------------------------------------------------------
    # Two tiers, deliberately kept apart: a contract is *invalidated* when an endpoint
    # source, an endpoint statement or the contract record itself changed; it is only
    # *at risk* when its endpoint project merely lost its editor admission. Collapsing
    # both into one signal would flag all contracts for every bridge change and hide
    # which ones actually moved.
    contract_rows = []
    invalidated_contracts = []
    at_risk_contracts = []
    for contract in records.contracts:
        groups: dict[str, dict] = {}
        unresolved: list[str] = []
        seen: dict[tuple[str, str], int] = {}
        endpoints = []
        for source_record in contract.sources:
            if source_record in changed_set:
                key = f"record:{source_record}"
                groups.setdefault(key, {"kind": "contract-record", "path": source_record})
        for lock_file in SEMANTIC_LOCK_FILES:
            if lock_file in changed_set:
                key = f"lock:{lock_file}"
                groups.setdefault(key, {"kind": "semantic-lock", "path": lock_file})
        for role, project_hint, name in contract.endpoints:
            project_name, source = records.resolve_endpoint(project_hint, name)
            resolved = None
            if project_name and source:
                resolved = records.projects[project_name].repo_path(source)
            # One row per (role, name): the two contract records store the same
            # endpoint once with and once without a project hint.
            slot = seen.get((role, name))
            row = {"role": role, "name": name, "project": project_name, "path": resolved}
            if slot is None:
                seen[(role, name)] = len(endpoints)
                endpoints.append(row)
            elif endpoints[slot]["project"] is None and project_name is not None:
                endpoints[slot] = row
            if resolved is None:
                unresolved.append(f"{project_hint or '?'}:{name}")
                continue
            if resolved in changed_set:
                key = f"endpoint-source:{role}:{resolved}"
                group = groups.setdefault(
                    key,
                    {"kind": "endpoint-source", "role": role, "path": resolved, "names": []},
                )
                if name not in group["names"]:
                    group["names"].append(name)
            if name in invalidated_ids:
                key = f"endpoint-node:{role}"
                group = groups.setdefault(key, {"kind": "endpoint-node", "role": role, "names": []})
                if name not in group["names"]:
                    group["names"].append(name)
            if project_name in voided:
                key = f"admission:{project_name}"
                groups.setdefault(key, {"kind": "admission", "project": project_name})
        for group in groups.values():
            if "names" in group:
                group["names"] = sorted(group["names"])
        # An endpoint whose source changed is already covered by the stronger
        # reason; do not repeat it as "statement invalidated" for the same role.
        updated_by_source = {
            (g["role"], name)
            for g in groups.values()
            if g["kind"] == "endpoint-source"
            for name in g["names"]
        }
        for key in [k for k, g in groups.items() if g["kind"] == "endpoint-node"]:
            group = groups[key]
            remaining = [n for n in group["names"] if (group["role"], n) not in updated_by_source]
            if remaining:
                group["names"] = remaining
            else:
                del groups[key]
        reasons = sorted(
            (g for g in groups.values() if g["kind"] != "admission"),
            key=lambda g: (g["kind"], g.get("role") or "", g.get("path") or "",
                           ",".join(g.get("names") or [])),
        )
        admission = sorted(
            (g["project"] for g in groups.values() if g["kind"] == "admission")
        )
        row = {
            "id": contract.id,
            "kind": contract.kind,
            "status": contract.status,
            "invalidated": bool(reasons),
            "at_risk": bool(admission),
            "reasons": reasons,
            "admission_lost": admission,
            "endpoints": sorted(endpoints, key=lambda e: (e["role"], e["name"])),
            "unresolved": sorted(unresolved),
        }
        contract_rows.append(row)
        if reasons:
            invalidated_contracts.append(row["id"])
        elif admission:
            at_risk_contracts.append(row["id"])

    # ---- 4. per-path classification ---------------------------------------------
    file_rows = []
    docs, unpinned, unclassified, outside = [], [], [], []
    for path in changed_paths:
        pin_rows = []
        for project_name in sorted(pins_by_project):
            for pin in pins_by_project[project_name]:
                if pin["path"] != path:
                    continue
                pin_rows.append(
                    {"project": project_name, "key": pin["key"], "kind": pin["kind"]}
                )
        classes = []
        if pin_rows:
            classes.append("project-input")
        if path in changed_set:
            for project in records.projects.values():
                if any(
                    node.source and project.repo_path(node.source) == path
                    for node in project.nodes.values()
                ) or any(
                    source and project.repo_path(source) == path
                    for source in project.catalog.values()
                ):
                    classes.append("theorem-source")
                    break
        if path in CONTRACT_RECORDS:
            classes.append("contract-record")
        if path in SEMANTIC_LOCK_FILES:
            classes.append("semantic-lock")
        if path.startswith("/") or ":" in path.split("/")[0][:3] or path.startswith("../"):
            classes.append("outside-repo")
            outside.append(path)
        elif not classes:
            lowered = path.lower()
            if lowered.endswith(DOC_SUFFIXES) or path.startswith(DOC_DIRS) or Path(path).name.lower().startswith("readme"):
                classes.append("documentation")
                docs.append(path)
            else:
                classes.append("unpinned")
                unpinned.append(path)
        else:
            if (
                path.lower().endswith(DOC_SUFFIXES)
                or path.startswith(DOC_DIRS)
                or Path(path).name.lower().startswith("readme")
            ) and "documentation" not in classes:
                docs.append(path)
        ordered = [name for name in CLASS_ORDER if name in classes]
        file_rows.append(
            {
                "path": path,
                "status": status_by_path.get(path, "?"),
                "primary_class": ordered[0] if ordered else "unpinned",
                "classes": ordered,
                "pins": pin_rows,
                "snapshot_member_of": sorted(member_of.get(path, ())),
            }
        )

    # ---- 5. statement-lock surface (what this tool cannot decide) -----------------
    pinned_in_files: dict[str, int] = {}
    for key, module in records.lock_modules.items():
        project_name = key.split(":", 1)[0]
        project = records.projects.get(project_name)
        if project is None:
            continue
        source = project.modules.get(module)
        if not source:
            continue
        repo_path = project.repo_path(source)
        if repo_path in changed_set:
            pinned_in_files[repo_path] = pinned_in_files.get(repo_path, 0) + 1
    statement_lock = {
        "records": ["bridges/statement-lock.json", "bridges/integrated-lock.json"],
        "pinned_by_project": records.statement_counts,
        "pinned_in_changed_files": dict(sorted(pinned_in_files.items())),
        "note": (
            "These hashes pin normalised elaborated statements. This tool cannot compare "
            "them: file hashes say nothing about whether a statement's meaning changed, "
            "and the pinned hash set is only refreshed by re-running the lock tool."
        ),
    }

    # ---- 6. counts and hand-reconstruction ledger --------------------------------
    counts = {
        "files": len(file_rows),
        "files_by_class": {
            name: sum(1 for row in file_rows if name in row["classes"])
            for name in CLASS_ORDER
            if any(name in row["classes"] for row in file_rows)
        },
        "receipts": len(receipts),
        "receipts_voided": sum(1 for row in receipts if row["void"]),
        "receipts_unknown": len(unknown),
        "snapshot_members_added": membership_added,
        "nodes_total": sum(len(project.nodes) for project in records.projects.values()),
        "nodes_direct": direct_total,
        "nodes_transitive_dependents": dependent_total,
        "nodes_invalidated": len(invalidated_ids),
        "nodes_to_pending": sum(row["nodes_to_pending"] for row in receipts),
        "contracts": len(contract_rows),
        "contracts_invalidated": len(invalidated_contracts),
        "contracts_at_risk": len(at_risk_contracts),
        "docs": len(docs),
        "unpinned": len(unpinned),
        "outside_repo": len(outside),
        "statement_hashes_in_changed_files": sum(pinned_in_files.values()),
    }
    hand = {
        "counts": {
            "nodes": counts["nodes_total"],
            "nodes_invalidated": counts["nodes_invalidated"],
            "nodes_to_pending": counts["nodes_to_pending"],
            "contracts": counts["contracts"],
            "contracts_invalidated": counts["contracts_invalidated"],
            "contracts_at_risk": counts["contracts_at_risk"],
            "receipts": counts["receipts"],
            "receipts_voided": counts["receipts_voided"],
            "receipts_unknown": counts["receipts_unknown"],
            "projects": len(records.projects),
        },
        "otherwise_manual": [
            f"{counts['receipts']} receipt(s) re-read against {len(changed_paths)} changed file(s) "
            f"to decide which pins they contain ({counts['receipts_voided']} void, "
            f"{counts['receipts_unknown']} undecidable)",
            f"{counts['receipts']} live input set(s) recomputed by calling each project's own "
            f"production snapshot function ({counts['snapshot_members_added']} new member(s) that "
            f"no recorded key covers)",
            f"{counts['nodes_total']} fact-tree nodes walked (depends_on + edges) to find the "
            f"{counts['nodes_invalidated']} whose evidence is no longer valid "
            f"({counts['nodes_to_pending']} more fall back to pending with a void receipt)",
            f"{counts['contracts']} cross-project contracts x their abstract/concrete/vendored "
            f"endpoints resolved to source files ({counts['contracts_invalidated']} invalidated, "
            f"{counts['contracts_at_risk']} at risk)",
            f"{counts['statement_hashes_in_changed_files']} statement-lock hashes located in the "
            f"touched files (their comparison still needs the lock tool, not this one)",
        ],
    }

    # ---- 7. redo list -------------------------------------------------------------
    redo: list[str] = []
    for row in receipts:
        if row["status"] != "UNKNOWN":
            continue
        detail = "; ".join(row["not_intact_because"])
        redo.append(
            f"{row['project']}: receipt UNKNOWN, the recorded observation cannot be shown to "
            f"cover the current input set ({detail})"
        )
    for row in receipts:
        if not row["void"]:
            continue
        project = records.projects[row["project"]]
        verifier = "verify_integrated.py" if row["schema"] == 3 else "verify.py"
        command = f"{project.rel + '/' if project.rel else ''}tools/{verifier}"
        key_list = sorted({f"{p['key']} ({p['kind']})" for p in row["pins"]})
        pins = ", ".join(key_list[:6])
        if len(key_list) > 6:
            pins += f", +{len(key_list) - 6} more"
        if not key_list:
            added = row["membership"]["added"]
            pins = "new snapshot input(s) no recorded key covers: " + ", ".join(
                f"{item['path']} ({item['origin']} set)" for item in added[:6]
            )
            if len(added) > 6:
                pins += f", +{len(added) - 6} more"
        redo.append(
            f"{row['project']}: re-run {command} and record a new editor observation; "
            f"{row['nodes_to_pending']} admitted node(s) return to pending [{pins}]"
        )
    for project_name in sorted(per_project):
        for path in sorted({row["source"] for row in per_project[project_name]["direct"] if row["source"]}):
            count = sum(1 for row in per_project[project_name]["direct"] if row["source"] == path)
            redo.append(f"{project_name}: re-verify + re-observe {path} ({count} node(s) sourced there)")
    if invalidated_contracts:
        redo.append(
            "re-audit contract(s) " + ", ".join(invalidated_contracts)
            + " (bridges/contracts.json / bridges/facts.json)"
        )
    if at_risk_contracts:
        redo.append(
            f"{len(at_risk_contracts)} further contract(s) stay unsupported until "
            + ", ".join(sorted({p for row in contract_rows for p in row["admission_lost"]}))
            + " is re-admitted: " + ", ".join(at_risk_contracts)
        )
    if pinned_in_files:
        redo.append(
            "re-lock statements with tools/semantic_lock.py and diff bridges/statement-lock.json; "
            f"{counts['statement_hashes_in_changed_files']} pinned name(s) live in the touched files"
        )
    if docs:
        redo.append(f"review {len(docs)} documentation file(s) by reading them (no machine evidence)")
    if unpinned:
        redo.append(f"read {len(unpinned)} unpinned change(s); decide whether evidence was rewritten by hand")
    if outside:
        redo.append(f"{len(outside)} path(s) outside the repository were ignored")

    return {
        "schema": 1,
        "tool": TOOL,
        "repo": str(root),
        "mode": mode,
        "changed": file_rows,
        "receipts": receipts,
        "theorems": {
            "per_project": per_project,
            "direct_count": direct_total,
            "dependent_count": dependent_total,
            "invalidated": sorted(invalidated_ids),
        },
        "contracts": {
            "total": len(contract_rows),
            "invalidated": sorted(invalidated_contracts),
            "at_risk": sorted(at_risk_contracts),
            "rows": contract_rows,
        },
        "docs": sorted(docs),
        "unpinned": sorted(unpinned),
        "unclassified": sorted(unclassified),
        "outside_repo": sorted(outside),
        "statement_lock": statement_lock,
        "snapshot_membership": {
            "probe": "enabled" if probe_membership else "disabled",
            "entry_points": {
                name: probe.as_row() for name, probe in sorted(probes.items())
            },
            "undecided": sorted(unknown),
            "note": (
                "Membership is not re-derived from glob patterns here: each project's own "
                "production snapshot function is imported and called, and each changed path "
                "is tested for membership in the live input (or dependency) set. "
                "A live member that no recorded key covers means the observation no longer "
                "spans the input set; a snapshot that cannot be computed leaves the receipt "
                "UNKNOWN instead of INTACT."
            ),
        },
        "counts": counts,
        "hand_reconstruction": hand,
        "redo": redo,
        "warnings": warnings,
    }


# --------------------------------------------------------------------------------------
# human rendering
# --------------------------------------------------------------------------------------
def render_human(payload: dict) -> str:
    out: list[str] = []
    add = out.append
    limit = HUMAN_ROW_LIMIT

    def elide(rows, what: str, prefix: str = "         ") -> None:
        if len(rows) > limit:
            add(f"{prefix}... {len(rows) - limit} more {what}; use --json for the complete list")
    mode = payload["mode"]
    if mode["kind"] == "range":
        head = f"range {mode['spec']}"
        if mode.get("commits"):
            head += f"  ({len(mode['commits'])} commit(s): " + ", ".join(
                f"{c['sha']} {c['subject']}" for c in mode["commits"]
            ) + ")"
    elif mode["kind"] == "staged":
        head = "staged index (git diff --cached)"
    else:
        head = f"explicit file list ({len(payload['changed'])} path(s))"
    add(f"{TOOL} -- incremental review scoping")
    add(f"repo     : {payload['repo']}")
    add(f"mode     : {head}")
    add(f"changed  : {payload['counts']['files']} file(s)")
    if payload["warnings"]:
        add("")
        add("WARNINGS")
        for warning in payload["warnings"]:
            add(f"  ! {warning}")

    add("")
    add("RECEIPTS  (does the recorded editor observation still bind?)")
    for row in payload["receipts"]:
        flag = {"VOID": "VOID   ", "UNKNOWN": "UNKNOWN", "INTACT": "INTACT "}.get(
            row["status"], row["status"])
        add(f"  {flag} {row['project']:<10} {row['path']}  schema={row['schema']}")
        for pin in row["pins"][:6]:
            add(f"         pin: {pin['key']}  ({pin['kind']})")
        if len(row["pins"]) > 6:
            add(f"         ... {len(row['pins']) - 6} more pin(s)")
        membership = row["membership"]
        input_block = (membership["probe"] or {}).get("input")
        if input_block and input_block["status"] == "decided":
            add(
                f"         live input set: {input_block['keys']} key(s) from "
                f"{input_block['source']}"
            )
        dependency_block = (membership["probe"] or {}).get("dependency")
        if dependency_block and dependency_block["status"] == "decided":
            add(
                f"         live dependency set: {dependency_block['keys']} key(s) from "
                f"{dependency_block['source']}"
            )
        for item in membership["added"][:limit]:
            add(
                f"         new snapshot member not covered by any recorded key: "
                f"{item['path']}  ({item['origin']} set)"
            )
        elide(membership["added"], "new snapshot member(s)")
        for reason in row["not_intact_because"]:
            add(f"         membership undecided: {reason}")
        if row["void"]:
            add(
                f"         {row['admitted_at_observation']} admitted node(s) -> "
                f"{row['nodes_to_pending']} back to pending"
            )

    theorems = payload["theorems"]["per_project"]
    add("")
    add("THEOREMS  (re-verify + re-observe)")
    if not theorems:
        add("  none: no fact-tree node's source changed")
    for project_name in sorted(theorems):
        block = theorems[project_name]
        add(
            f"  {project_name}: {block['direct_count']} direct, "
            f"{block['dependent_count']} transitive dependent(s)"
        )
        for row in block["direct"][:limit]:
            add(f"         changed source : {row['id']}  [{row['source']}]")
        elide(block["direct"], "direct node(s)")
        for row in block["dependents"][:limit]:
            add(f"         depends on it  : {row['id']}  [{row['source']}]")
        elide(block["dependents"], "transitive dependent(s)")
        if block["receipt_void"]:
            add(f"         whole receipt void -> {len(block['admitted_to_pending'])} admitted node(s) pending")

    add("")
    add("CONTRACTS  (cross-project, must be re-audited)")
    contracts = payload["contracts"]
    if not contracts["invalidated"] and not contracts["at_risk"]:
        add(f"  none of {contracts['total']} contract(s) affected")
    shown_contracts = 0
    for row in contracts["rows"]:
        if not row["invalidated"] and not row["at_risk"]:
            continue
        shown_contracts += 1
        if shown_contracts > limit:
            continue
        verdict = "INVALIDATED" if row["invalidated"] else "at risk"
        add(f"  {row['id']}  {verdict}  kind={row['kind']}  recorded_status={row['status']}")
        for reason in row["reasons"]:
            kind = reason["kind"]
            if kind == "endpoint-source":
                add(f"         {reason['role']} endpoint source changed  [{reason['path']}]")
            elif kind == "endpoint-node":
                add(f"         {reason['role']} endpoint statement invalidated")
            elif kind == "contract-record":
                add(f"         contract record changed  [{reason['path']}]")
            elif kind == "semantic-lock":
                add(f"         semantic lock ledger changed  [{reason['path']}]")
            for name in reason.get("names") or []:
                add(f"           - {name}")
        for project_name in row["admission_lost"]:
            add(f"         endpoints lose admission until {project_name} is re-admitted")
        for name in row["unresolved"]:
            add(f"         unresolved endpoint: {name}")
    affected_contracts = len(contracts["invalidated"]) + len(contracts["at_risk"])
    if affected_contracts > limit:
        add(f"  ... {affected_contracts - limit} more contract(s); use --json for the complete list")

    add("")
    add("CHANGED FILES  (classification)")
    for row in payload["changed"][:limit]:
        add(f"  {row['status']} {row['path']}  -> {', '.join(row['classes'])}")
        for pin in row["pins"]:
            add(f"       pinned by {pin['project']} as {pin['key']} ({pin['kind']})")
        if row.get("snapshot_member_of"):
            add(f"       live snapshot member of: {', '.join(row['snapshot_member_of'])}")
    elide(payload["changed"], "file(s)", prefix="  ")
    if payload["counts"].get("files_by_class"):
        add("  by class: " + ", ".join(
            f"{name}={count}" for name, count in payload["counts"]["files_by_class"].items()))

    if payload["docs"]:
        add("")
        add("DOCUMENTATION  (no machine evidence invalidated, reviewer reads)")
        for path in payload["docs"][:limit]:
            add(f"  {path}")
        elide(payload["docs"], "documentation file(s)", prefix="  ")
    if payload["unpinned"]:
        add("")
        add("UNPINNED  (no receipt pins these: verify they did not rewrite evidence by hand)")
        for path in payload["unpinned"][:limit]:
            add(f"  {path}")
        elide(payload["unpinned"], "unpinned change(s)", prefix="  ")
    if payload["outside_repo"]:
        add("")
        add("OUTSIDE REPOSITORY  (ignored)")
        for path in payload["outside_repo"][:limit]:
            add(f"  {path}")
        elide(payload["outside_repo"], "path(s) outside the repository", prefix="  ")

    add("")
    add("WHAT ASTRA WOULD OTHERWISE HAVE TO RECONSTRUCT BY HAND")
    counts = payload["hand_reconstruction"]["counts"]
    add(
        f"  {counts['receipts']} receipts ({counts['receipts_voided']} void, "
        f"{counts['receipts_unknown']} undecidable) - "
        f"{counts['contracts']} contracts ({counts['contracts_invalidated']} invalidated, "
        f"{counts['contracts_at_risk']} at risk) - "
        f"{counts['nodes']} nodes ({counts['nodes_invalidated']} invalidated, "
        f"{counts['nodes_to_pending']} -> pending) across {counts['projects']} projects"
    )
    for line in payload["hand_reconstruction"]["otherwise_manual"]:
        add(f"  - {line}")
    lock = payload["statement_lock"]
    add(
        "  statement pinning is NOT covered here: "
        + ", ".join(f"{name}:{count}" for name, count in lock["pinned_by_project"].items())
        + " pinned names; see bridges/statement-lock.json"
    )

    add("")
    add("WHAT MUST BE REDONE")
    if not payload["redo"]:
        add("  nothing: no recorded evidence is invalidated by this change set")
    for index, step in enumerate(payload["redo"], 1):
        add(f"  {index}. {step}")
    return "\n".join(out)


# --------------------------------------------------------------------------------------
# cli
# --------------------------------------------------------------------------------------
def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="audit/affected.py",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=(
            "Incremental review scoping: report which recorded evidence a change set "
            "invalidates, and what must be redone."
        ),
        epilog=(
            "Selection modes (exactly one):\n"
            "  --range A..B     compare two commits (git diff --name-status, plus git log for context)\n"
            "  --files P ...    explicit repository-relative paths (deleted paths are fine)\n"
            "  --staged         the staged index (git diff --cached)\n\n"
            "Read-only: this tool never writes, never builds and never runs a verifier.\n"
            "Membership of a changed path in a project's live input set is decided by\n"
            "importing that project's own production snapshot function (read-only hashing),\n"
            "so the glob rules are never re-implemented here.  --no-membership-probe skips\n"
            "that step and then no receipt can be called INTACT (they become UNKNOWN).\n\n"
            "Exit status: 0 analysed, 1 analysis failed, 2 bad arguments.\n\n"
            "Note on Windows: the tool writes UTF-8 without a BOM, but Windows PowerShell\n"
            "5.x '>' redirection re-encodes native output as UTF-16LE.  For --json use a\n"
            "cmd.exe redirect or '| Out-File -Encoding utf8' if a consumer cannot read it.\n\n"
            "Examples:\n"
            "  python audit/affected.py --range 78bc059..HEAD\n"
            "  python audit/affected.py --files bridge/IUTBridge/Admissibility.lean --json\n"
            "  python audit/affected.py --staged\n"
        ),
    )
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--range", dest="range_spec", metavar="A..B",
                           help="commit range to compare, e.g. 78bc059..HEAD")
    selection.add_argument("--files", dest="files", nargs="+", metavar="PATH",
                           help="explicit repository-relative paths")
    selection.add_argument("--staged", dest="staged", action="store_true",
                           help="use the staged index")
    parser.add_argument("--json", dest="as_json", action="store_true",
                        help="machine-readable output on stdout")
    parser.add_argument("--no-membership-probe", dest="no_membership_probe",
                        action="store_true",
                        help="do not call the production snapshot functions (every non-void "
                             "receipt is then reported UNKNOWN, never INTACT)")
    parser.add_argument("--repo", dest="repo", metavar="PATH", default=None,
                        help="repository root (default: the parent of this script's directory)")
    return parser


def main(argv: list[str] | None = None) -> int:
    if hasattr(sys.stdout, "reconfigure"):
        try:
            sys.stdout.reconfigure(encoding="utf-8", errors="replace")
            sys.stderr.reconfigure(encoding="utf-8", errors="replace")
        except (OSError, ValueError):  # pragma: no cover - unusual streams
            pass

    parser = build_parser()
    args = parser.parse_args(argv)
    if not (args.range_spec or args.files or args.staged):
        parser.error("one of --range, --files or --staged is required")

    try:
        root = Path(args.repo).resolve() if args.repo else Path(__file__).resolve().parents[1]
        if not root.is_dir():
            raise ToolError(f"repository root does not exist: {root}")
        toplevel = git_toplevel(root)

        if args.range_spec:
            if toplevel is None:
                raise ToolError(f"not a git repository: {root}")
            changes, commits = changes_from_range(root, toplevel, args.range_spec)
            mode = {"kind": "range", "spec": args.range_spec, "commits": commits,
                    "commit_count": len(commits)}
        elif args.staged:
            if toplevel is None:
                raise ToolError(f"not a git repository: {root}")
            changes = changes_from_staged(root, toplevel)
            mode = {"kind": "staged", "commits": []}
        else:
            changes = changes_from_files(root, toplevel or root, args.files)
            mode = {"kind": "files", "paths": sorted({c.path for c in changes}), "commits": []}

        records = Records.load(root)
        payload = analyse(records, changes, mode,
                          probe_membership=not args.no_membership_probe)
    except ToolError as exc:
        print(f"{TOOL}: error: {exc}", file=sys.stderr)
        return 1

    if args.as_json:
        print(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=False))
    else:
        print(render_human(payload))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
