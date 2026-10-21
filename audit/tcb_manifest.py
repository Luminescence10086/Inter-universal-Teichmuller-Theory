#!/usr/bin/env python3
"""tcb_manifest.py - discover a verifier's real read set, compare it to the pin.

Policy ("minimal trusted computing base", cf. seLSA / SLSA provenance scoping):
a Lean project ships ``verification/checked-inputs.json`` whose
``input_sha256`` map is bound by an editor receipt; admitting fact-tree nodes
requires that receipt to validate, so *every* key in that map is load-bearing
for admission.  Pinning a file the verifier never interprets turns an unrelated
edit into a voided observation (brittleness), while failing to pin a file the
verifier does interpret leaves a silent evidence gap.

Every discovered read site is classified:

  READ (consumed)   the verifier's decision depends on the file's *content*:
                    json.load(s) / read_text / read_bytes / open / a Lean
                    source handed to the toolchain via subprocess / a sibling
                    module imported (hence executed) / the verifier source
                    itself.
  PIN-ONLY          the file is enumerated by a snapshot glob and handed to a
                    hash function inside the pin builder, but no consumer ever
                    interprets it: its content cannot change any decision.
                    Over-pinning.
  OBSERVATION       the editor receipt / observation log the verifier
                    validates.  It cannot sit inside the map it validates
                    (circular), so it is reported, never silently dropped.
  RUNTIME/EXTERNAL  OLean artifacts, toolchain binaries, external git
                    checkouts: bound by runtime_sha256 / recorded commit, not
                    by the input map.

Static discovery is deliberately conservative and *self-reporting*.  A path
built from runtime data (f-string, dict subscript, value read out of JSON) is
recorded as UNRESOLVED and the process exits 3, so an incomplete closure can
never be mistaken for a complete one.  A dynamic segment that the same function
constrains with a regex literal is resolved by matching that regex against the
tree (the ``verification/vscode-observation-roundN.txt`` handshake does this).

Closure completeness (acceptance finding R1/P1)
-----------------------------------------------
A read site this analyser does not model is *not* evidence that a pin is
unnecessary.  Every consumer boundary that cannot be traversed is therefore
recorded as INCOMPLETE, with the category it belongs to:

  executed-program    a subprocess runs a repo-local program or script; that
                      program's own read set is never analysed here
  dynamic-command     the argv of an exec is not statically known
  lean-build         ``lake build`` / ``lake env lean <file>.lean`` hands Lean
                      sources and their import graph to the toolchain: a
                      runtime/Lean read this Python analyser cannot observe
  module-method-call  a ``module.func(...)`` call whose body was not resolved
  unsupported-call    a call on an unknown receiver or an unknown callee
  unreached-consumer  a module-level function main() never calls, although
                      other components may (``freshness.verifier(base)`` calls
                      ``module.snapshot()``)
  unanalysed-entry    a standalone or pinned Python component outside the
                      analysed closure, e.g. ``tools/semantic_lock.py``, which
                      executes ``lake env lean ... tools/DefinitionBodies.lean``
  module-cap / depth-cap   a coverage cap was hit

If at least one such boundary exists (or an UNRESOLVED repo-scoped read site),
the closure is INCOMPLETE and the tool refuses to emit a safe-to-remove pin
proposal.  It then reports

    proposal.status        == "WITHHELD"
    proposal.withheld_reason == "closure incomplete — proposal withheld"
    proposal.removed       == []            (no deletion is suggested)
    proposal.proposed_pin  == current pin   (the existing rule is kept)

and a pinned key with no discovered consumer is reported as UNCLASSIFIED --
never as proof of uselessness.  Input, dependency, runtime and toolchain
consumption are reported in separate categories, so a Lean source in the
dependency map is toolchain consumption rather than "only Python hashes it".

Exit codes: 0 = clean closure, no findings; 2 = over/under-pinned findings on a
complete closure; 3 = at least one unresolved repo-scoped dynamic read site;
4 = closure incomplete (unsupported consumer boundary): proposal withheld.

Usage:
    python audit/tcb_manifest.py                       # all three projects
    python audit/tcb_manifest.py --project bridge --json
    python audit/tcb_manifest.py --project bridge --propose

Read-only: nothing is written anywhere; the proposal goes to stdout.
"""

from __future__ import annotations

import argparse
import ast
import builtins
import hashlib
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

# --------------------------------------------------------------------------
# policy tables
# --------------------------------------------------------------------------

#: site kinds whose content the verifier's decisions depend on
CONSUMING_KINDS = frozenset(
    {"read_text", "read_bytes", "open", "exec", "import", "digest-check",
     "regex-read"}
)

#: inputs the lake/lean toolchain reads implicitly for the invocations the
#: verifier performs.  Not discoverable by static analysis, declared instead.
PLATFORM_INPUTS = frozenset({"lean-toolchain", "lakefile.toml",
                             "lake-manifest.json"})

KNOWN_HELPERS = frozenset({"run", "save", "digest", "check_process",
                           "one_information"})

#: method names that cannot read a file: calling them on an unresolved receiver
#: is not a consumer boundary (hashing, string/list/dict plumbing).
PURE_METHODS = frozenset({
    "encode", "decode", "join", "pop", "sort", "reverse", "copy", "count",
    "index", "issubset", "issuperset", "union", "intersection", "difference",
    "add", "discard", "clear", "keys", "values", "items", "get", "setdefault",
    "format", "splitlines", "partition", "casefold", "title", "capitalize",
    "strip", "lstrip", "rstrip", "lower", "upper", "replace", "startswith",
    "endswith", "split", "rsplit", "removesuffix", "removeprefix", "ljust",
    "rjust", "zfill", "isoformat", "append", "extend", "update", "sort_key",
    "groupby", "isinstance",
    # pathlib plumbing on an unresolved path value: it only re-shapes a path,
    # so it is not a consumer boundary (a later read/digest still surfaces as
    # UNRESOLVED through consume()).
    "resolve", "absolute", "expanduser", "as_posix", "relative_to", "joinpath",
    "exists", "is_file", "is_dir", "is_absolute", "is_symlink", "iterdir",
    "with_name", "with_suffix", "with_stem", "stat", "glob", "rglob",
    "mkdir", "unlink", "touch", "readlink",
})

#: programs that interpret a source file handed to them on the command line
PYTHON_PROGRAMS = frozenset({"python", "python3", "py", "python2"})

#: programs that are part of the Lean toolchain
LEAN_PROGRAMS = frozenset({"lake", "lean"})

#: dependency-map entries the Lean toolchain (not Python) interprets
LEAN_SOURCE_SUFFIXES = (".lean", ".olean")
LEAN_CONFIG_NAMES = frozenset({"lean-toolchain", "lakefile.toml",
                               "lakefile.lean", "lake-manifest.json"})

#: builtins a verifier may call without opening anything; a call to any other
#: unresolved name is an unsupported consumer boundary (never silent).
PURE_BUILTINS = frozenset(dir(builtins)) - {
    "open", "__import__", "exec", "eval", "compile", "input", "breakpoint",
    "globals", "locals", "memoryview",
}

PROJECTS = {
    "root": ".",
    "local-field": "local-field",
    "bridge": "bridge",
}

EXEMPT_DIRS = {"reviews", ".git", ".lake", "__pycache__",
               ".tmp-round2-verifier", ".agent-notes"}

MAX_INLINE_DEPTH = 6
MAX_MODULES = 40
MAX_JSON_BYTES = 8_000_000


def map_for_function(name: str) -> str | None:
    """Which pin map a snapshot builder feeds."""
    if "snapshot" not in name:
        return None
    return "dependency_sha256" if "depend" in name else "input_sha256"


def is_snapshot_fn(name: str) -> bool:
    return "snapshot" in name or name == "<module>"


def is_main_guard(test: ast.AST) -> bool:
    """True for `__name__ == '__main__'`."""
    if not isinstance(test, ast.Compare) or len(test.ops) != 1:
        return False
    if not isinstance(test.left, ast.Name) or test.left.id != "__name__":
        return False
    comparator = test.comparators[0]
    return isinstance(comparator, ast.Constant) and comparator.value == "__main__"


# --------------------------------------------------------------------------
# symbolic values
# --------------------------------------------------------------------------

@dataclass(frozen=True)
class P:
    """Symbolic path relative to the project directory.

    ``parts`` may contain '..' (``ROOT.parent / 'tools'`` is
    ``('..', 'tools')``); ``glob`` is a Path.glob pattern to expand; ``unknown``
    records why a segment could not be evaluated statically.
    """

    parts: tuple = ()
    glob: str | None = None
    unknown: str | None = None


@dataclass(frozen=True)
class Unk:
    reason: str
    detail: str = ""
    #: set when the unknown value is an imported module that has no local file
    #: (standard library / third party): a call on it is not a repo consumer
    foreign: str | None = None


@dataclass(frozen=True)
class ModuleRef:
    """A name bound to a sibling module file that *was* loaded and analysed."""

    rel: str


@dataclass(frozen=True)
class Content:
    """Text read from a known file.  Lets ``json.loads`` resolve real values so
    catalog-driven loops and receipt lookups stay visible instead of looking
    dead."""

    key: str


class KeyDict(dict):
    """A dict produced by a snapshot comprehension: remembers the path objects
    it was built from, so iterating it recovers real pin keys instead of
    losing them to string formatting."""

    path_items: list = []


def p_child(p: P, seg: str) -> P:
    return P(p.parts + (seg,), p.glob, p.unknown)


def p_parent(p: P, times: int = 1) -> P:
    parts = list(p.parts)
    for _ in range(times):
        if parts and parts[-1] != "..":
            parts.pop()
        else:
            parts.append("..")
    return P(tuple(parts), p.glob, p.unknown)


def p_unknown(p: P, reason: str) -> P:
    return P(p.parts, p.glob, p.unknown or reason)


def as_list(value) -> list:
    if isinstance(value, list):
        return list(value)
    if isinstance(value, (P, Unk)):
        return [value]
    return []


@dataclass
class Site:
    kind: str
    display: str
    keys: tuple
    file: str
    line: int
    snippet: str
    fn: str
    map: str | None = None


@dataclass
class Unresolved:
    display: str
    reason: str
    file: str
    line: int
    snippet: str
    fn: str
    scope: str


@dataclass
class Boundary:
    """A consumer boundary this analyser could not traverse.

    It never proves a pin useless: it proves our closure is *incomplete*, which
    is why an incomplete closure suppresses the removal proposal.
    """

    kind: str
    category: str            # "consumer" | "toolchain"
    detail: str
    file: str
    line: int
    snippet: str
    fn: str

    def as_dict(self) -> dict:
        return {"kind": self.kind, "category": self.category,
                "detail": self.detail, "file": self.file, "line": self.line,
                "snippet": self.snippet, "fn": self.fn}


@dataclass
class FunctionInfo:
    node: ast.FunctionDef
    module: "ModuleInfo"
    env: dict


@dataclass
class ModuleInfo:
    name: str
    rel: str
    path: Path
    tree: ast.Module
    env: dict = field(default_factory=dict)


# --------------------------------------------------------------------------
# analyzer
# --------------------------------------------------------------------------

class Analyzer:
    def __init__(self, project: Path):
        self.project = project.resolve()
        self.functions: dict[str, FunctionInfo] = {}
        self.modules: dict[str, ModuleInfo] = {}
        self.sites: list[Site] = []
        self.unresolved: list[Unresolved] = []
        self.boundaries: list[Boundary] = []
        self.writes: list[str] = []
        self.external: set[str] = set()
        self.regex_hints: dict[tuple, list[str]] = {}
        self.stack: list[str] = []
        self.returns: list = []
        self.depth = 0
        self.analyzing: set[str] = set()
        self.module_rel_parts: tuple = ()
        self.map_stack: list = [None]
        self._module: ModuleInfo | None = None
        self._unresolved_seen: set = set()
        self._boundary_seen: set = set()
        self.entered: set = set()
        self.module_defs: set = set()
        self.functions_by_module: dict = {}
        self.entry_rel: str = "tools/verify.py"

    # -- helpers -----------------------------------------------------------

    def current_fn(self) -> str:
        return self.stack[-1] if self.stack else "<module>"

    def current_map(self) -> str | None:
        for m in reversed(self.map_stack):
            if m:
                return m
        return None

    def rel(self, p: Path) -> str:
        try:
            return p.resolve().relative_to(self.project).as_posix()
        except ValueError:
            return str(p)

    def key_for(self, p: Path) -> str:
        """Mirror the verifier's own key convention (relative, else @workspace/)."""
        rp = Path(p).resolve()
        try:
            return rp.relative_to(self.project).as_posix()
        except ValueError:
            pass
        try:
            return "@workspace/" + rp.relative_to(self.project.parent).as_posix()
        except ValueError:
            return rp.as_posix()

    def snippet(self, node: ast.AST) -> str:
        try:
            text = ast.unparse(node)
        except Exception:  # pragma: no cover
            text = type(node).__name__
        text = " ".join(text.split())
        return text if len(text) <= 130 else text[:127] + "..."

    def render(self, value) -> str:
        if isinstance(value, P):
            text = "/".join(value.parts) if value.parts else "<project>"
            if value.glob:
                text += f" + glob({value.glob!r})"
            if value.unknown:
                text += f"  [unresolved: {value.unknown}]"
            return text
        if isinstance(value, ModuleRef):
            return f"<module {value.rel}>"
        if isinstance(value, Unk):
            return f"<{value.reason}>"
        if isinstance(value, str):
            return repr(value)
        if isinstance(value, list):
            return "[" + ", ".join(self.render(v) for v in value[:4]) + "]"
        if isinstance(value, dict):
            return "{" + ", ".join(sorted(value)[:4]) + "}"
        return f"<{type(value).__name__}>"

    # -- module loading ----------------------------------------------------

    def analyze_project(self, entry_rel: str) -> None:
        entry = self.project / entry_rel
        if not entry.is_file():
            raise SystemExit(f"error: verifier not found: {entry}")
        self.entry_rel = entry_rel
        module = self.load_module(entry)
        # the verifier's own source is executed: it is part of the TCB
        if module is not None:
            self.sites.append(Site(
                kind="import", display=entry_rel, keys=(self.key_for(entry),),
                file=entry_rel, line=0, fn="<module>", map="input_sha256",
                snippet="# verifier entry point (executed source)"))
        if "main" in self.functions:
            self.call_named("main")

    def load_module(self, path: Path) -> ModuleInfo | None:
        path = Path(path).resolve()
        if len(self.modules) >= MAX_MODULES:
            self.add_boundary(
                "module-cap", "consumer",
                f"MAX_MODULES={MAX_MODULES} reached; {self.rel(path)} was not "
                f"analysed", where=self.rel(path))
            return None
        rel = self.rel(path)
        if rel in self.modules:
            return self.modules[rel]
        if rel in self.analyzing:
            return None
        self.analyzing.add(rel)
        try:
            source = path.read_text(encoding="utf-8")
            tree = ast.parse(source, filename=str(path))
        except SyntaxError as exc:  # loud, never silent
            raise SystemExit(f"error: cannot parse {rel}: {exc}")
        module = ModuleInfo(name=path.stem, rel=rel, path=path, tree=tree)
        self.modules[rel] = module
        prev_module, prev_rel = self._module, self.module_rel_parts
        saved_stack = self.stack
        self._module = module
        self.module_rel_parts = tuple(path.relative_to(self.project).parts)
        self.stack = []
        self.walk(tree.body, module.env, module)   # module level executes
        self.stack = saved_stack
        self._module, self.module_rel_parts = prev_module, prev_rel
        self.analyzing.discard(rel)
        return module

    # -- read-site recording ----------------------------------------------

    def read_site(self, pv, kind: str, node: ast.AST):
        """Record a content read; return a Content token when the file is known."""
        display = self.render(pv)
        if not isinstance(pv, P):
            self.consume(pv, kind, node)
            return Unk("file content")
        keys, why = self.resolve(pv)
        if why is not None:
            scope = "empty-glob" if why.startswith("glob ") else None
            self.add_unresolved(display, why, node, scope=scope)
            return Unk(why)
        self.add_site(kind, display, tuple(keys), node)
        return Content(keys[0]) if len(keys) == 1 else Unk("file content")

    def load_json(self, content) -> "object":
        if not isinstance(content, Content):
            return Unk("json content")
        path = pin_target(content.key, self.project)
        try:
            if not path.is_file() or path.stat().st_size > MAX_JSON_BYTES:
                return Unk("json content")
            return json.loads(path.read_text(encoding="utf-8"))
        except (OSError, ValueError, UnicodeDecodeError):
            return Unk("json content")

    def consume(self, value, kind: str, node: ast.AST, env: dict | None = None) -> None:
        display = self.render(value)
        if isinstance(value, P):
            keys, why = self.resolve(value)
            if why is not None:
                # an empty glob means the verifier read nothing there, which is
                # the safe direction: record it, but do not call it a gap.
                scope = "empty-glob" if why.startswith("glob ") else None
                self.add_unresolved(display, why, node, scope=scope)
                return
            self.add_site(kind, display, tuple(keys), node)
            return
        if isinstance(value, Unk):
            self.add_unresolved(display, value.reason, node)
            return
        if isinstance(value, str):
            cand = self.project / value
            if cand.is_file():
                self.add_site(kind, display, (self.key_for(cand),), node)
            return
        for item in as_list(value):
            self.consume(item, kind, node)

    def add_site(self, kind: str, display: str, keys: tuple, node: ast.AST):
        self.sites.append(Site(
            kind=kind, display=display, keys=tuple(keys),
            file=self._module.rel if self._module else "<unknown>",
            line=getattr(node, "lineno", 0), snippet=self.snippet(node),
            fn=self.current_fn(), map=self.current_map()))

    def add_unresolved(self, display: str, reason: str, node: ast.AST,
                       scope: str | None = None):
        fn = self.current_fn()
        if scope is None:
            if fn == "external_git_identity":
                scope = "external-checkout"
            elif fn in ("runtime_snapshot", "project_snapshot_imports"):
                scope = "runtime-oleans"
            else:
                scope = "repo"
        record = Unresolved(
            display=display, reason=reason,
            file=self._module.rel if self._module else "<unknown>",
            line=getattr(node, "lineno", 0), snippet=self.snippet(node),
            fn=fn, scope=scope)
        key = (record.file, record.line, record.reason, record.scope)
        if key in self._unresolved_seen:
            return
        self._unresolved_seen.add(key)
        self.unresolved.append(record)

    def add_boundary(self, kind: str, category: str, detail: str,
                     node: ast.AST | None = None, where: str | None = None):
        """Record a consumer boundary that static analysis cannot traverse.

        Boundaries never justify a pin removal; they set closure.complete=False.
        """
        fn = self.current_fn()
        record = Boundary(
            kind=kind, category=category, detail=detail,
            file=self._module.rel if self._module else (where or "<unknown>"),
            line=getattr(node, "lineno", 0) if node is not None else 0,
            snippet=self.snippet(node) if node is not None else "",
            fn=fn)
        key = (record.kind, record.file, record.line, record.detail)
        if key in self._boundary_seen:
            return
        self._boundary_seen.add(key)
        self.boundaries.append(record)

    # -- resolution --------------------------------------------------------

    def resolve(self, pv: P) -> tuple[list[str], str | None]:
        if pv.unknown:
            keys = self.regex_resolve(pv)
            if keys:
                return keys, None
            return [], pv.unknown
        base = self.project.joinpath(*pv.parts) if pv.parts else self.project
        if pv.glob:
            try:
                base_resolved = Path(base).resolve()
                matches = sorted(base_resolved.glob(pv.glob))
            except (ValueError, OSError):
                return [], f"invalid glob {pv.glob!r}"
            files = [m for m in matches if m.is_file()]
            if not files:
                return [], (f"glob {pv.glob!r} matched no file under "
                            f"{self.rel(Path(base))}")
            return [self.key_for(f) for f in files], None
        base = Path(base).resolve()
        if base.is_file():
            return [self.key_for(base)], None
        return [], f"not a file on disk: {self.rel(Path(base))}"

    def regex_resolve(self, pv: P) -> list[str]:
        patterns = self.regex_hints.get(
            (self._module.rel if self._module else "", self.current_fn()), [])
        if not patterns:
            return []
        out: list[str] = []
        for path in self.iter_tree():
            rel = self.rel(path)
            for pat in patterns:
                try:
                    if re.fullmatch(pat, rel):
                        out.append(self.key_for(path))
                        break
                except re.error:
                    continue
        return sorted(set(out))

    def iter_tree(self):
        for path in sorted(self.project.rglob("*")):
            if not path.is_file():
                continue
            if EXEMPT_DIRS & set(path.parts):
                continue
            yield path

    # -- expression evaluator ---------------------------------------------

    def ev(self, node, env: dict, module: ModuleInfo | None = None):
        if node is None:
            return None
        module = module or self._module
        if isinstance(node, ast.Constant):
            return node.value
        if isinstance(node, ast.Name):
            if node.id in env:
                return env[node.id]
            if node.id == "__file__":
                return P(self.module_rel_parts)
            return Unk(f"name {node.id}")
        if isinstance(node, ast.Attribute):
            return self.ev_attr(node, env, module)
        if isinstance(node, ast.Subscript):
            return self.ev_subscript(node, env, module)
        if isinstance(node, ast.BinOp):
            return self.ev_binop(node, env, module)
        if isinstance(node, (ast.BoolOp, ast.Compare)):
            for child in ast.iter_child_nodes(node):
                if isinstance(child, ast.expr):
                    self.ev(child, env, module)
            return Unk("bool")
        if isinstance(node, ast.UnaryOp):
            self.ev(node.operand, env, module)
            return Unk("unary")
        if isinstance(node, ast.Call):
            return self.ev_call(node, env, module)
        if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
            return [self.ev(e, env, module) for e in node.elts]
        if isinstance(node, ast.Dict):
            out = {}
            for k, v in zip(node.keys, node.values):
                kv = self.ev(k, env, module) if k is not None else Unk("key")
                vv = self.ev(v, env, module)
                if isinstance(kv, str):
                    out[kv] = vv
            return out
        if isinstance(node, (ast.ListComp, ast.SetComp, ast.GeneratorExp,
                             ast.DictComp)):
            return self.ev_comp(node, env, module)
        if isinstance(node, ast.IfExp):
            a = self.ev(node.body, env, module)
            if isinstance(a, Unk):
                # `x = f(...) if cond else {}` must stay unresolved, not
                # collapse to the empty fallback (that would hide reads)
                self.ev(node.orelse, env, module)
                return a
            b = self.ev(node.orelse, env, module)
            return b if isinstance(b, Unk) else a
        if isinstance(node, ast.JoinedStr):
            return Unk("f-string path (computed dynamically)")
        if isinstance(node, ast.NamedExpr):
            value = self.ev(node.value, env, module)
            self.bind_target(node.target, value, env)
            return value
        if isinstance(node, ast.Starred):
            return self.ev(node.value, env, module)
        return Unk(type(node).__name__)

    def ev_attr(self, node, env, module):
        base = self.ev(node.value, env, module)
        attr = node.attr
        if isinstance(base, Unk) and base.foreign is not None:
            if base.foreign == "sys" and attr == "executable":
                return Unk("interpreter sys.executable")
            return Unk(f"foreign attribute {attr}", foreign=base.foreign)
        if isinstance(base, ModuleRef):
            return Unk(f"module attribute {attr}", detail=base.rel)
        if isinstance(base, P):
            if attr == "parent":
                return p_parent(base)
            if attr == "parents":
                return base
            if attr in ("name", "stem", "suffix"):
                return Unk(f"path.{attr}")
        if isinstance(base, dict) and attr in ("keys", "values", "items"):
            # dict(x.items()) / sorted(x.items()) round-trips: keep the key
            # provenance so iterating a pin map recovers real keys.
            return base
        return Unk(f"attribute {attr}")

    def ev_subscript(self, node, env, module):
        if isinstance(node.value, ast.Attribute) and node.value.attr == "parents":
            base = self.ev(node.value.value, env, module)
            idx = self.ev(node.slice, env, module)
            if isinstance(base, P) and isinstance(idx, int):
                # pathlib: file.parents[0] is the containing directory
                return p_parent(base, idx + 1)
            return Unk("parents[<dynamic>]")
        base = self.ev(node.value, env, module)
        key = self.ev(node.slice, env, module)
        if isinstance(base, dict) and isinstance(key, str):
            if key in base:
                return base[key]
            return Unk("dict lookup", key)
        if isinstance(base, (list, tuple)) and isinstance(key, int):
            try:
                return base[key]
            except IndexError:
                return Unk("index out of range")
        if isinstance(base, Unk):
            return base
        return Unk("subscript on runtime data")

    def ev_binop(self, node, env, module):
        left = self.ev(node.left, env, module)
        right = self.ev(node.right, env, module)
        op = type(node.op).__name__
        if op == "Div":
            if isinstance(left, P) and isinstance(right, str):
                return p_child(left, right)
            if isinstance(left, P) and isinstance(right, Unk):
                return p_unknown(left, right.reason)
            return Unk("/ on runtime data")
        if op == "Add":
            if isinstance(left, list):
                return left + as_list(right)
            if isinstance(left, str) and isinstance(right, str):
                return Unk("string concatenation")
            return Unk("add")
        if op == "BitOr":
            out = as_list(left)
            out.extend(as_list(right))
            return out
        return Unk(f"binop {op}")

    def ev_call(self, node, env, module):
        func = node.func
        if isinstance(func, ast.Name):
            return self.ev_call_name(node, func.id, env, module)
        if isinstance(func, ast.Attribute):
            return self.ev_call_attr(node, func, env, module)
        for a in node.args:
            self.ev(a, env, module)
        return Unk("call")

    def ev_call_name(self, node, name, env, module):
        args = node.args
        if name == "Path":
            if not args:
                return Unk("Path()")
            a0 = args[0]
            if isinstance(a0, ast.Name) and a0.id == "__file__":
                return P(self.module_rel_parts)
            value = self.ev(a0, env, module)
            if isinstance(value, P):
                return value
            if isinstance(value, str):
                return P(tuple(Path(value).parts))
            return Unk("Path(runtime data)")
        if name in ("set", "list", "tuple", "sorted", "reversed", "iter",
                    "enumerate"):
            if args:
                value = self.ev(args[0], env, module)
                return as_list(value) if isinstance(value, (P, Unk)) else value
            return []
        if name == "dict":
            value = self.ev(args[0], env, module) if args else {}
            return value if isinstance(value, dict) else {}
        if name == "open":
            if args:
                return self.read_site(self.ev(args[0], env, module), "open", node)
            return Unk("file content")
        if name == "digest":
            self.entered.add(name)
            kind = ("hash-only" if is_snapshot_fn(self.current_fn())
                    else "digest-check")
            if args:
                self.consume(self.ev(args[0], env, module), kind, node)
            return Unk("sha256 hex")
        if name == "run":                        # subprocess wrapper
            self.entered.add(name)
            if args:
                self.do_argv(self.ev(args[0], env, module), node)
            for a in args[1:]:
                self.ev(a, env, module)
            return Unk("stdout")
        if name in ("one_information", "check_process"):
            self.entered.add(name)
            # pure wrappers: their arguments still execute the subprocess
            for a in args:
                self.ev(a, env, module)
            return Unk("helper")
        if name == "save":
            self.entered.add(name)
            return Unk("write")
        if name in ("min", "max", "len", "any", "all", "print", "range",
                    "isinstance", "getattr", "vars", "hasattr", "hashlib"):
            for a in args:
                self.ev(a, env, module)
            return Unk(name)
        if name == "str":
            if args:
                value = self.ev(args[0], env, module)
                if isinstance(value, P):
                    return value          # str(path) is still that path
                if isinstance(value, Unk):
                    return value
            return Unk("str()")
        return self.call_local(node, name, env, module)

    def ev_call_attr(self, node, func, env, module):
        attr = func.attr
        base = self.ev(func.value, env, module)
        args = node.args
        if isinstance(base, ModuleRef):
            return self.call_sibling(base, attr, node, env, module)
        if isinstance(base, P):
            if attr in ("glob", "rglob"):
                pat = self.ev(args[0], env, module) if args else Unk("pattern")
                if isinstance(pat, str):
                    return P(base.parts, pat)
                return p_unknown(base, getattr(pat, "reason", "glob pattern"))
            if attr in ("read_text", "read_bytes"):
                return self.read_site(base, "read_text", node)
            if attr == "open":
                return self.read_site(base, "open", node)
            if attr in ("write_text", "write_bytes", "write", "mkdir",
                        "unlink", "touch"):
                self.writes.append(self.render(base))
                return None
            if attr in ("resolve", "absolute", "expanduser", "relative_to",
                        "as_posix"):
                return base
            if attr == "joinpath":
                out = base
                for a in args:
                    seg = self.ev(a, env, module)
                    if isinstance(seg, str):
                        out = p_child(out, seg)
                    else:
                        out = p_unknown(out, "joinpath segment")
                return out
            if attr in ("exists", "is_file", "is_dir"):
                return True
            if attr == "iterdir":
                return P(base.parts, "*")
            if attr == "stat":
                return Unk("stat")
            if attr in ("with_name", "with_suffix"):
                return p_unknown(base, f"path.{attr}")
        if isinstance(base, dict):
            if attr in ("get", "setdefault"):
                key = self.ev(args[0], env, module) if args else None
                if isinstance(key, str) and key in base:
                    return base[key]
                if len(args) > 1:
                    return self.ev(args[1], env, module)
                return Unk("dict.get(runtime key)")
            if attr in ("items", "keys", "values"):
                return base      # keep pin-map key provenance through dict()
        if attr in ("update", "append", "extend", "add"):
            self.mutate(func.value, args, env, module)
            return None
        if attr in ("strip", "lower", "upper", "removesuffix", "replace",
                    "rsplit", "split", "startswith", "endswith", "format"):
            return Unk(f"str.{attr}")
        if attr in ("fullmatch", "match", "search", "findall", "sub",
                    "compile"):
            self.record_regex_hint(args)
            for a in args:
                self.ev(a, env, module)
            return Unk("regex result")
        if attr == "run":
            if args:
                self.do_argv(self.ev(args[0], env, module), node)
            return Unk("CompletedProcess")
        if attr == "which":
            if args:
                v = self.ev(args[0], env, module)
                if isinstance(v, str):
                    self.external.add(v)
            return Unk("tool path", v if isinstance(v, str) else "")
        if attr in ("loads", "load"):
            content = self.ev(args[0], env, module) if args else Unk("json")
            return self.load_json(content)
        if attr in ("file_digest", "sha256", "new", "dumps",
                    "hexdigest", "file"):
            for a in args:
                self.ev(a, env, module)
            return Unk(f"call {attr}")
        if isinstance(base, Unk) and base.foreign is not None:
            # a standard-library / third-party call: it does not read repo inputs
            for a in args:
                self.ev(a, env, module)
            return Unk(f"foreign method {attr}", foreign=base.foreign)
        if attr in PURE_METHODS:
            for a in args:
                self.ev(a, env, module)
            return Unk(f"pure method {attr}")
        for a in args:
            self.ev(a, env, module)
        # Unsupported consumer boundary: we cannot see what this method reads.
        self.add_boundary(
            "unsupported-call", "consumer",
            f"method call .{attr}(...) on {self.render(base)} cannot be "
            f"resolved; any file it reads is invisible to this analysis", node)
        return Unk(f"method {attr}")

    def call_sibling(self, ref: ModuleRef, attr: str, node, env, module):
        """`import helper; helper.check(ROOT)` - inline the sibling function.

        Ordinary module method calls are part of the closure: without this the
        callee's reads are silently missing (acceptance review R1/P1).
        """
        arg_values = [self.ev(a, env, module) for a in node.args]
        info = self.functions_by_module.get(ref.rel, {}).get(attr)
        if info is None:
            if self.depth >= MAX_INLINE_DEPTH:
                self.add_boundary(
                    "depth-cap", "consumer",
                    f"call depth cap reached resolving {ref.rel}:{attr}()", node)
                return Unk("depth cap")
            self.add_boundary(
                "module-method-call", "consumer",
                f"{ref.rel} has no analysed definition of {attr}(); its body "
                f"was not traversed", node)
            return Unk(f"module method {attr}")
        if self.depth >= MAX_INLINE_DEPTH:
            self.add_boundary(
                "depth-cap", "consumer",
                f"call depth cap reached inlining {ref.rel}:{attr}()", node)
            return Unk("depth cap")
        return self.inline(info, env, module, arg_values=arg_values,
                           args_node=node)

    def record_regex_hint(self, args) -> None:
        if not args:
            return
        v = args[0]
        if isinstance(v, ast.Constant) and isinstance(v.value, str):
            key = (self._module.rel if self._module else "", self.current_fn())
            self.regex_hints.setdefault(key, []).append(v.value)

    def mutate(self, target, args, env, module):
        if not isinstance(target, ast.Name) or not args:
            for a in args:
                self.ev(a, env, module)
            return
        current = env.get(target.id)
        addition = self.ev(args[0], env, module)
        if isinstance(current, list):
            current.extend(as_list(addition))
        else:
            env[target.id] = as_list(addition)

    def program_name(self, item) -> str | None:
        """Best-effort identity of the program at argv[0]."""
        if isinstance(item, str):
            name = item.replace("\\", "/").rsplit("/", 1)[-1].lower()
            return name.removesuffix(".exe")
        if isinstance(item, Unk):
            if item.reason == "tool path" and isinstance(item.detail, str):
                return item.detail.lower().removesuffix(".exe")
            if item.reason.endswith("sys.executable"):
                return "python"
        return None

    def do_argv(self, value, node) -> None:
        if isinstance(value, P):
            self.consume(value, "exec", node)
            self.add_boundary(
                "executed-program", "consumer",
                f"executes repo program {self.render(value)}; that program's "
                f"read set is not analysed", node)
            return
        if not isinstance(value, list):
            self.add_boundary(
                "dynamic-command", "consumer",
                "exec argv is not statically known; the executed program and "
                "its reads are invisible", node)
            return
        strings = [v for v in value if isinstance(v, str)]
        program = self.program_name(value[0]) if value else None
        lean_sources = [s for s in strings if s.endswith(".lean")]
        if lean_sources or (program in LEAN_PROGRAMS and "build" in strings):
            detail = "Lean toolchain invocation " + " ".join(
                ([program or "<tool>"] + strings)[:6])
            if lean_sources:
                detail += "; the Lean import graph of " + ", ".join(
                    lean_sources[:4]) + " is not analysed"
            else:
                detail += "; a Lean build reads the whole import graph"
            self.add_boundary("lean-build", "toolchain", detail, node)
        executed = []
        for i, item in enumerate(value):
            if i == 0:                      # program: an external tool
                if isinstance(item, str):
                    self.external.add(item)
                elif isinstance(item, Unk) and isinstance(item.detail, str) \
                        and item.reason == "tool path":
                    self.external.add(item.detail)
                continue
            if isinstance(item, str):
                cand = self.project / item
                if cand.is_file():          # cwd = project: executed source
                    self.add_site("exec", repr(item),
                                  (self.key_for(cand),), node)
                    if item.endswith((".py", ".pyw")):
                        executed.append(item)
                continue
            if isinstance(item, P):
                keys, why = self.resolve(item)
                if why is not None and why.startswith("not a file"):
                    # e.g. `git -C <checkout dir>`: a directory target, not a read
                    if Path(self.project.joinpath(*item.parts)).is_dir():
                        continue
                self.consume(item, "exec", node)
            elif isinstance(item, (Unk, list)):
                self.consume(item, "exec", node)
        if executed:
            self.add_boundary(
                "executed-program", "consumer",
                "subprocess executes repo script "
                + ", ".join(sorted(set(executed)))
                + "; that script's own read closure is not analysed here", node)
        elif program in PYTHON_PROGRAMS:
            self.add_boundary(
                "dynamic-command", "consumer",
                "a Python interpreter runs code this analyser cannot see "
                "(inline -c / shell string); its reads are invisible", node)

    # -- comprehensions ----------------------------------------------------

    def ev_comp(self, node, env, module):
        results: list = []
        pairs: list = []
        outer_items: list = []

        def rec(i: int, current: dict):
            if i == len(node.generators):
                if isinstance(node, ast.DictComp):
                    pairs.append((self.ev(node.key, current, module),
                                  self.ev(node.value, current, module)))
                else:
                    results.append(self.ev(node.elt, current, module))
                return
            gen = node.generators[i]
            seq = self.ev(gen.iter, current, module)
            items = self.items_of(seq)
            if i == 0:
                outer_items.extend(items)
            if gen.ifs and items and all(isinstance(x, str) for x in items):
                varname = gen.target.id if isinstance(gen.target, ast.Name) else None
                preds = []
                if varname:
                    for cond in gen.ifs:
                        pred = self.str_filter(cond, varname)
                        if pred is None:
                            preds = []
                            break
                        preds.append(pred)
                if preds:
                    items = [x for x in items if all(p(x) for p in preds)]
            for item in items:
                inner = dict(current)
                self.bind_target(gen.target, item, inner)
                for cond in gen.ifs:
                    self.ev(cond, inner, module)
                rec(i + 1, inner)

        rec(0, dict(env))
        if isinstance(node, ast.DictComp):
            out = KeyDict()
            for k, v in pairs:
                if isinstance(k, str):
                    out[k] = v
            if outer_items and all(isinstance(x, P) for x in outer_items):
                out.path_items = list(outer_items)
            return out
        return results

    def items_of(self, seq) -> list:
        if isinstance(seq, KeyDict):
            if seq.path_items:
                keys: list[str] = []
                for pv in seq.path_items:
                    resolved, _ = self.resolve(pv)
                    keys.extend(resolved)
                if keys:
                    return keys
            return list(seq.keys())
        if isinstance(seq, dict):
            return list(seq.keys())
        if isinstance(seq, list):
            return list(seq)
        if isinstance(seq, (P, str)):
            return [seq]
        return []

    def str_filter(self, cond, varname):
        """Extract ``name.endswith('x')``-style predicates, so iterating a pin
        map's keys does not over-approximate the executed set."""
        if isinstance(cond, ast.BoolOp):
            preds = [self.str_filter(v, varname) for v in cond.values]
            if any(p is None for p in preds):
                return None
            if isinstance(cond.op, ast.And):
                return lambda s: all(p(s) for p in preds)
            return lambda s: any(p(s) for p in preds)
        if isinstance(cond, ast.UnaryOp) and isinstance(cond.op, ast.Not):
            inner = self.str_filter(cond.operand, varname)
            return (lambda s: not inner(s)) if inner else None
        if isinstance(cond, ast.Call) and isinstance(cond.func, ast.Attribute):
            f = cond.func
            if (isinstance(f.value, ast.Name) and f.value.id == varname
                    and f.attr in ("endswith", "startswith")
                    and len(cond.args) == 1
                    and isinstance(cond.args[0], ast.Constant)
                    and isinstance(cond.args[0].value, str)):
                affix = cond.args[0].value
                if f.attr == "endswith":
                    return lambda s, t=affix: s.endswith(t)
                return lambda s, t=affix: s.startswith(t)
        if (isinstance(cond, ast.Compare) and len(cond.ops) == 1
                and isinstance(cond.ops[0], ast.Eq)
                and isinstance(cond.left, ast.Name)
                and cond.left.id == varname
                and isinstance(cond.comparators[0], ast.Constant)):
            lit = cond.comparators[0].value
            return lambda s, lit=lit: s == lit
        return None

    # -- statements --------------------------------------------------------

    def bind_target(self, target, value, env: dict) -> None:
        if isinstance(target, ast.Name):
            env[target.id] = value
            return
        if isinstance(target, (ast.Tuple, ast.List)):
            if isinstance(value, list) and len(value) == len(target.elts):
                for t, v in zip(target.elts, value):
                    self.bind_target(t, v, env)
            else:
                for t in target.elts:
                    self.bind_target(t, Unk("unpacked"), env)
            return
        if isinstance(target, ast.Subscript):
            self.ev(target.value, env, self._module)
            return
        if isinstance(target, ast.Attribute):
            self.ev(target.value, env, self._module)

    def walk(self, stmts, env: dict, module: ModuleInfo) -> None:
        for stmt in stmts:
            self.stmt(stmt, env, module)

    def stmt(self, node, env: dict, module: ModuleInfo) -> None:
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            self.do_import(node, env, module)
            return
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            info = FunctionInfo(node, module, env)
            self.functions[node.name] = info
            self.functions_by_module.setdefault(module.rel, {})[node.name] = info
            if not self.stack:
                self.module_defs.add(node.name)
            return
        if isinstance(node, ast.ClassDef):
            return
        if isinstance(node, ast.Assign):
            value = self.ev(node.value, env, module)
            for target in node.targets:
                self.bind_target(target, value, env)
            return
        if isinstance(node, ast.AnnAssign):
            if node.value is not None:
                self.bind_target(node.target, self.ev(node.value, env, module), env)
            return
        if isinstance(node, ast.AugAssign):
            self.aug_assign(node, env, module)
            return
        if isinstance(node, ast.Expr):
            self.ev(node.value, env, module)
            return
        if isinstance(node, ast.Return):
            if node.value is not None:
                value = self.ev(node.value, env, module)
                if self.returns and self.returns[-1] is None:
                    self.returns[-1] = value
            return
        if isinstance(node, ast.For):
            items = self.items_of(self.ev(node.iter, env, module))
            for item in items:
                self.bind_target(node.target, item, env)
                self.walk(node.body, env, module)
            self.walk(node.orelse, env, module)
            return
        if isinstance(node, ast.While):
            self.ev(node.test, env, module)
            self.walk(node.body, env, module)
            return
        if isinstance(node, ast.If):
            # `if __name__ == '__main__':` only runs for the entry script; main()
            # is invoked explicitly, so walking it here would double-count.
            if is_main_guard(node.test):
                return
            self.ev(node.test, env, module)
            self.walk(node.body, dict(env), module)
            self.walk(node.orelse, dict(env), module)
            return
        if isinstance(node, ast.Try):
            self.walk(node.body, env, module)
            for handler in node.handlers:
                self.walk(handler.body, dict(env), module)
            self.walk(node.orelse, env, module)
            self.walk(node.finalbody, env, module)
            return
        if isinstance(node, ast.With):
            for item in node.items:
                self.ev(item.context_expr, env, module)
                if item.optional_vars is not None:
                    self.bind_target(item.optional_vars, Unk("context"), env)
            self.walk(node.body, env, module)
            return
        if isinstance(node, ast.Match):
            self.ev(node.subject, env, module)
            for case in node.cases:
                self.walk(case.body, dict(env), module)
            return
        if isinstance(node, ast.Assert):
            self.ev(node.test, env, module)
            return
        if isinstance(node, ast.Raise):
            if node.exc is not None:
                self.ev(node.exc, env, module)
            return
        for child in ast.iter_child_nodes(node):
            if isinstance(child, ast.expr):
                self.ev(child, env, module)

    def aug_assign(self, node, env, module):
        if not isinstance(node.target, ast.Name):
            self.ev(node.value, env, module)
            return
        current = env.get(node.target.id)
        op = type(node.op).__name__
        addition = self.ev(node.value, env, module)
        if op == "Add":
            if isinstance(current, list):
                env[node.target.id] = current + as_list(addition)
            elif isinstance(current, str) and isinstance(addition, str):
                env[node.target.id] = current + addition
            else:
                env[node.target.id] = current
        elif op == "BitOr":
            merged = as_list(current)
            merged.extend(as_list(addition))
            env[node.target.id] = merged
        else:
            env[node.target.id] = current

    # -- imports -----------------------------------------------------------

    def do_import(self, node, env, module: ModuleInfo) -> None:
        if isinstance(node, ast.ImportFrom):
            names = [node.module.split(".")[0]] if node.module else []
        else:
            names = [a.name.split(".")[0] for a in node.names]
        found: dict = {}
        for base in names:
            target = module.path.parent / f"{base}.py"
            if not target.is_file():
                found[base] = None
                continue
            rel = self.rel(target)
            self.sites.append(Site(
                kind="import", display=rel, keys=(self.key_for(target),),
                file=module.rel, line=getattr(node, "lineno", 0),
                snippet=self.snippet(node), fn=self.current_fn(),
                map=self.current_map()))
            self.load_module(target)
            found[base] = rel
        # Bind the imported names: a sibling module becomes a ModuleRef (so
        # `helper.check(ROOT)` can be inlined), anything else is a foreign
        # module whose calls cannot read repo inputs.
        if isinstance(node, ast.ImportFrom):
            primary = names[0] if names else None
            if primary:
                env[primary] = (ModuleRef(found[primary]) if found.get(primary)
                                else Unk(f"foreign module {primary}",
                                         foreign=primary))
            for alias in node.names:
                bind = alias.asname or alias.name
                if bind == "*":
                    continue
                env[bind] = Unk(f"imported name {bind}",
                                foreign=primary or bind)
        else:
            for alias in node.names:
                base = alias.name.split(".")[0]
                bind = alias.asname or base
                if found.get(base):
                    env[bind] = ModuleRef(found[base])
                else:
                    env[bind] = Unk(f"foreign module {base}", foreign=base)

    # -- function calls ----------------------------------------------------

    def call_named(self, name: str) -> None:
        info = self.functions.get(name)
        if info is None:
            raise SystemExit(f"error: no {name}() found in the verifier closure")
        self.entered.add(name)
        self.inline(info, {}, None, forced_env=None, args_node=None)

    def call_local(self, node, name: str, env, module):
        arg_values = [self.ev(a, env, module) for a in node.args]
        for a in node.args:
            self.ev(a, env, module)
        info = self.functions.get(name)
        if info is None:
            if name in PURE_BUILTINS:
                return Unk(f"builtin {name}()")
            # Unsupported consumer boundary: an unresolved callee could read
            # anything, so the closure cannot be called complete.
            self.add_boundary(
                "unsupported-call", "consumer",
                f"call to {name}() resolves to no analysed function and is not "
                f"a known builtin; its reads are invisible", node)
            return Unk(f"external call {name}()")
        if self.depth >= MAX_INLINE_DEPTH:
            self.add_unresolved(name, "call depth exceeded (inlining cap)", node)
            return Unk("depth cap")
        return self.inline(info, env, module, arg_values=arg_values,
                           args_node=node)

    def inline(self, info: FunctionInfo, env, module, args_node=None,
               arg_values=None, forced_env=None):
        if self.depth >= MAX_INLINE_DEPTH:
            self.add_boundary(
                "depth-cap", "consumer",
                f"call depth cap MAX_INLINE_DEPTH={MAX_INLINE_DEPTH} reached "
                f"inlining {info.node.name}(); deeper reads are not analysed")
            return Unk("depth cap")
        self.depth += 1
        local = dict(info.module.env)
        params = [a.arg for a in info.node.args.args]
        values = arg_values or []
        defaults = info.node.args.defaults
        first_default = len(params) - len(defaults)
        for i, pname in enumerate(params):
            if i < len(values):
                local[pname] = values[i]
            elif i >= first_default:
                local[pname] = self.ev(defaults[i - first_default],
                                       info.module.env, info.module)
            else:
                local[pname] = Unk("default arg")
        if args_node is not None:
            for kw in args_node.keywords:
                if kw.arg:
                    local[kw.arg] = self.ev(kw.value, env, module)
        saved_module = self._module
        self._module = info.module
        self.returns.append(None)
        self.stack.append(info.node.name)
        self.entered.add(info.node.name)
        self.map_stack.append(map_for_function(info.node.name))
        self.walk(info.node.body, local, info.module)
        value = self.returns.pop()
        self.map_stack.pop()
        self.stack.pop()
        self._module = saved_module
        self.depth -= 1
        return value if value is not None else Unk("no return value")


# --------------------------------------------------------------------------
# report
# --------------------------------------------------------------------------

def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def pin_target(key: str, project: Path) -> Path:
    if key.startswith("@workspace/"):
        return project.parent / key[len("@workspace/"):]
    return project / key


def abs_key(key: str, project: Path) -> str | None:
    """Normalise any pin key / site key to an absolute posix path."""
    try:
        if key.startswith("@workspace/"):
            return (project.parent / key[len("@workspace/"):]).resolve().as_posix()
        candidate = Path(key)
        if candidate.is_absolute() or (len(key) > 1 and key[1] == ":"):
            return candidate.resolve().as_posix()
        return (project / key).resolve().as_posix()
    except (OSError, ValueError):
        return None


def classify(key: str, project: Path | None = None) -> str:
    """input | observation | output | external."""
    base = key.rsplit("/", 1)[-1]
    in_verification = ("/verification/" in key or key.startswith("verification/")
                       or key.startswith("@workspace/verification/"))
    if in_verification and (base.startswith("vscode-") or base.endswith("receipt.json")):
        return "observation"
    if in_verification:
        return "output"
    if project is not None:
        try:
            if key.startswith("@workspace/"):
                path = project.parent / key[len("@workspace/"):]
            elif len(key) > 1 and key[1] == ":" or key.startswith("/"):
                path = Path(key)
            else:
                path = project / key
            path = Path(path).resolve()
            try:
                path.relative_to(project)
            except ValueError:
                # outside the project: inside the workspace, or a foreign
                # checkout bound by commit rather than by the input map
                try:
                    path.relative_to(project.parent)
                except ValueError:
                    return "external"
        except (OSError, ValueError):
            pass
    return "input"


def is_toolchain_input(key: str) -> bool:
    """True when the Lean toolchain (not this Python analyser) interprets it."""
    base = key.replace("\\", "/").rsplit("/", 1)[-1]
    return base.endswith(LEAN_SOURCE_SUFFIXES) or base in LEAN_CONFIG_NAMES


def collect(analyzer: Analyzer, kinds: frozenset) -> dict:
    buckets: dict[str, list[Site]] = {}
    for site in analyzer.sites:
        if site.kind in kinds:
            for key in site.keys:
                buckets.setdefault(key, []).append(site)
    return buckets


# --------------------------------------------------------------------------
# closure completeness
# --------------------------------------------------------------------------

WITHHELD_REASON = "closure incomplete — proposal withheld"

CLOSURE_CRITERIA = (
    "complete means every consumer boundary in the traversed closure was "
    "resolved: the executed verifier, its imports and inlined calls, every "
    "executed program, every sibling-module call, and every Lean build input. "
    "Any boundary this analyser cannot traverse makes the closure incomplete.")


def has_standalone_entry(path: Path) -> bool:
    """True when a module can run on its own (``main()`` or __main__ guard)."""
    try:
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    except (OSError, SyntaxError, UnicodeDecodeError):
        return False
    for stmt in tree.body:
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)) \
                and stmt.name == "main":
            return True
        if isinstance(stmt, ast.If) and is_main_guard(stmt.test):
            return True
    return False


def scan_unanalysed_entry_points(analyzer, project_dir: Path,
                                 input_pin: dict) -> list:
    """Python components outside the analysed closure that may read inputs.

    Two families are reported instead of being ignored:

    * a standalone entry point under this project's ``tools/`` directory;
    * a pinned ``@workspace/tools/*.py`` component.  It is part of the
      evidence chain by construction (the pin records it) yet its body was
      never walked -- e.g. ``tools/semantic_lock.py`` runs
      ``lake env lean ... tools/DefinitionBodies.lean``.
    """
    found: list = []
    own = project_dir / "tools"
    if own.is_dir():
        for path in sorted(own.rglob("*.py")):
            if "__pycache__" in path.parts or not path.is_file():
                continue
            rel = analyzer.rel(path)
            if rel in analyzer.modules:
                continue
            if has_standalone_entry(path):
                found.append({
                    "path": rel, "key": None, "display": rel,
                    "reason": "standalone entry point (main()/__main__ guard) "
                              "outside the tools/verify.py closure; its body and "
                              "anything it reads or executes are not analysed"})
    shared = project_dir.parent / "tools"
    if shared.is_dir() and shared.resolve() != own.resolve():
        for key in sorted(input_pin):
            if not key.startswith("@workspace/tools/") or not key.endswith(".py"):
                continue
            path = pin_target(key, project_dir)
            rel = analyzer.rel(path)
            if rel in analyzer.modules:
                continue
            if not path.is_file():
                continue
            found.append({
                "path": rel, "key": key, "display": key,
                "reason": "pinned @workspace Python component outside the "
                          "analysed closure; its body is never walked, so any "
                          "file it reads or executes is invisible to this "
                          "analysis"})
    return found


def build_closure(analyzer, project_dir: Path, input_pin: dict) -> dict:
    """Decide whether the analysed closure is complete, and why not."""
    unresolved_repo = [u for u in analyzer.unresolved if u.scope == "repo"]
    entries = scan_unanalysed_entry_points(analyzer, project_dir, input_pin)
    boundaries = [b.as_dict() for b in analyzer.boundaries]
    for entry in entries:
        boundaries.append({
            "kind": "unanalysed-entry", "category": "consumer",
            "detail": entry["reason"], "file": entry.get("display") or entry["path"],
            "line": 0, "snippet": entry.get("key") or "", "fn": "<entry>"})
    # "uncovered consumers": module-level functions main() never calls.  Known
    # primitive wrappers (run/digest/save/check_process/one_information) are
    # handled explicitly by the analyser, so they are not listed here.
    for name in sorted(analyzer.module_defs):
        if name in analyzer.entered or name in KNOWN_HELPERS:
            continue
        info = None
        for rel in sorted(analyzer.functions_by_module):
            if name in analyzer.functions_by_module[rel]:
                info = analyzer.functions_by_module[rel][name]
                break
        boundaries.append({
            "kind": "unreached-consumer", "category": "consumer",
            "detail": f"{name}() is defined but main() never calls it; another "
                      f"component may (freshness.verifier(base) calls "
                      f"module.snapshot()), so its reads are not covered",
            "file": info.module.rel if info else "<unknown>",
            "line": getattr(info.node, "lineno", 0) if info else 0,
            "snippet": f"def {name}(...)", "fn": "<module>"})
    kinds = sorted({b["kind"] for b in boundaries})
    reasons = []
    if kinds:
        reasons.append("unsupported consumer boundaries: " + ", ".join(kinds))
    if unresolved_repo:
        reasons.append(f"{len(unresolved_repo)} unresolved repo-scoped dynamic "
                       f"read site(s)")
    counts: dict = {}
    for b in boundaries:
        counts[b["kind"]] = counts.get(b["kind"], 0) + 1
    complete = not boundaries and not unresolved_repo
    return {
        "complete": complete,
        "status": "complete" if complete else "incomplete",
        "entry_points": {
            "analyzed": [{"path": analyzer.entry_rel,
                          "how": "executed verifier source; main() inlined",
                          "modules": sorted(analyzer.modules)}],
            "not_analyzed": entries,
        },
        "boundaries": boundaries,
        "boundary_counts": counts,
        "unsupported_boundaries": kinds,
        "unresolved_repo_sites": [
            {"expr": u.display, "reason": u.reason, "file": u.file,
             "line": u.line, "fn": u.fn} for u in unresolved_repo],
        "reasons": reasons,
        "criteria": CLOSURE_CRITERIA,
        "safe_removal_proposal_allowed": complete,
        "proposal_withheld_reason": None if complete else WITHHELD_REASON,
    }


def analyze_project(project_dir: Path, name: str) -> dict:
    project_dir = Path(project_dir).resolve()
    analyzer = Analyzer(project_dir)
    analyzer.analyze_project("tools/verify.py")

    pin_file = project_dir / "verification" / "checked-inputs.json"
    input_pin: dict = {}
    dep_pin: dict = {}
    if pin_file.is_file():
        data = json.loads(pin_file.read_text(encoding="utf-8"))
        if isinstance(data.get("input_sha256"), dict):
            input_pin = data["input_sha256"]
        if isinstance(data.get("dependency_sha256"), dict):
            dep_pin = data["dependency_sha256"]

    read = collect(analyzer, CONSUMING_KINDS)
    pin_only = collect(analyzer, frozenset({"hash-only"}))
    platform = sorted(k for k in input_pin if k in PLATFORM_INPUTS)

    closure = build_closure(analyzer, project_dir, input_pin)

    # ---- input map -------------------------------------------------------
    # "no consumer site found" is NEVER proof of uselessness: when the closure
    # is incomplete the entries become UNCLASSIFIED instead of over-pinned.
    no_consumer = []
    for key in sorted(input_pin):
        if key in read or key in platform:
            continue
        evidence = []
        for s in pin_only.get(key, []):
            text = f"{s.kind} via {s.display} at {s.file}:{s.line}"
            if text not in evidence:
                evidence.append(text)
        path = pin_target(key, project_dir)
        exists = path.is_file()
        if evidence:
            reason = ("hash-only: enumerated and hashed by the pin builder, but "
                      "no consumer site interprets its content")
        elif exists:
            reason = "no read site discovered anywhere in the verifier closure"
        else:
            reason = "no read site discovered and the key is absent on disk"
        no_consumer.append({"key": key, "sha256": input_pin[key], "reason": reason,
                            "evidence": evidence, "exists": exists})

    if closure["complete"]:
        over = no_consumer
        unclassified = []
    else:
        over = []
        unclassified = [
            dict(entry, classification="unclassified",
                 reason=entry["reason"]
                        + "; closure incomplete -> unclassified, not a claim "
                          "that the pin is unnecessary")
            for entry in no_consumer]

    under, exempt, dep_covered = [], [], []
    for key in sorted(read):
        if key in input_pin or key in platform:
            continue
        sites = read[key]
        kind = classify(key, project_dir)
        if kind == "external":
            # foreign checkout: bound by recorded commit / config_sha256
            exempt.append({"key": key, "kind": "external",
                           "sites": [{"file": s.file, "line": s.line,
                                      "kind": s.kind, "snippet": s.snippet,
                                      "map": s.map} for s in sites]})
            continue
        if sites and all(s.map == "dependency_sha256" for s in sites):
            # bound by the dependency map, not the input map: not a gap here
            dep_covered.append(key)
            continue
        record = {
            "key": key,
            "kind": kind,
            "sites": [{"file": s.file, "line": s.line, "kind": s.kind,
                       "snippet": s.snippet, "map": s.map}
                      for s in sites],
        }
        if kind in ("observation", "output", "external"):
            record["kind"] = kind
            exempt.append(record)
        else:
            under.append(record)

    # ---- dependency map --------------------------------------------------
    # Categories are kept apart: a Python read of the map is NOT the whole
    # story for a Lean source, which the Lean import/build graph consumes.
    dep_report: dict = {}
    dep_read_abs: dict = {}
    dep_unclassified: list = []
    dep_toolchain: list = []
    if dep_pin:
        dep_sites: dict[str, list[Site]] = {}
        for site in analyzer.sites:
            if site.kind in CONSUMING_KINDS and site.map == "dependency_sha256":
                for key in site.keys:
                    dep_sites.setdefault(key, []).append(site)
        dep_read_abs = {}
        for key, sites in dep_sites.items():
            if classify(key, project_dir) == "external":
                continue          # foreign checkout: bound by commit, not by hash
            ab = abs_key(key, project_dir)
            if ab:
                dep_read_abs.setdefault(ab, []).extend(sites)
        dep_pinned_abs = {}
        synthetic = []
        for key in sorted(dep_pin):
            ab = abs_key(key, project_dir)
            if ab and Path(key).suffix and Path(key).is_file():
                dep_pinned_abs[ab] = key
            elif ab and (project_dir.parent / key[len("@workspace/"):]).is_file() \
                    if key.startswith("@workspace/") else False:
                dep_pinned_abs[ab] = key
            elif ab and Path(key).is_file():
                dep_pinned_abs[ab] = key
            else:
                synthetic.append(key)
        for ab in sorted(dep_pinned_abs):
            if ab in dep_read_abs:
                continue
            key = dep_pinned_abs[ab]
            if is_toolchain_input(key):
                dep_toolchain.append({
                    "key": key, "category": "toolchain",
                    "reason": "the Lean import/build graph interprets this "
                              "source or config; the Python verifier merely "
                              "hashes it, which is not evidence that the "
                              "toolchain leaves it unused"})
            else:
                dep_unclassified.append({
                    "key": key, "category": "dependency",
                    "reason": "no Python consumer site discovered in this "
                              "closure; unclassified, not evidence of "
                              "uselessness (an outer tool may read it)"})
        dep_under = [{"key": k, "abs": ab,
                      "sites": [f"{s.file}:{s.line}" for s in v]}
                     for ab, v in sorted(dep_read_abs.items())
                     for k in [next((x for x in dep_pin if abs_key(x, project_dir) == ab),
                                    ab)]
                     if ab not in dep_pinned_abs]
        dep_report = {
            "pinned": len(dep_pin),
            "read": len(dep_read_abs),
            "over_pinned": 0,
            "under_pinned": len(dep_under),
            "over": [],
            "under": dep_under,
            "unclassified": dep_unclassified,
            "toolchain_consumed": dep_toolchain,
            "synthetic_keys": synthetic,
            "note": "no dependency-map key is proposed for removal; a Lean "
                    "source here is toolchain consumption, not a Python-"
                    "hash-only artefact",
        }

    proposal = build_proposal(project_dir, input_pin, read, platform, over,
                              dep_covered, closure)

    admissions: dict = {}
    facts = project_dir / "fact-tree" / "facts.json"
    if facts.is_file():
        try:
            data = json.loads(facts.read_text(encoding="utf-8"))
            admissions = {"admitted": len(data.get("nodes", [])),
                          "status": data.get("status"),
                          "pending": data.get("pending_count")}
        except (json.JSONDecodeError, OSError, UnicodeDecodeError):
            admissions = {}

    unresolved_repo = [u for u in analyzer.unresolved if u.scope == "repo"]
    # honesty: module-level functions never reached from main() cannot have
    # contributed read sites, so say so instead of implying a full closure.
    module_functions = set(analyzer.module_defs)
    unreached = sorted(name for name in module_functions
                       if name not in analyzer.entered)
    exempt_keys = {e["key"] for e in exempt}

    # ---- categories ------------------------------------------------------
    # input / dependency / runtime / toolchain are reported separately and no
    # category may speak for another: a Lean source is toolchain consumption,
    # not "only Python hashes it".
    consumed_input = sorted(k for k in input_pin if k in read)
    categories = {
        "input": {
            "pinned": len(input_pin),
            "consumed": len(consumed_input),
            "declared_platform_inputs": len(platform),
            "unclassified": len(unclassified),
            "absent_on_disk": sum(1 for o in no_consumer if not o["exists"]),
        },
        "dependency": {
            "pinned": len(dep_pin),
            "consumed_python": len(dep_read_abs),
            "unclassified": len(dep_unclassified),
            "toolchain_consumed": len(dep_toolchain),
        },
        "runtime": {
            "external_tools": sorted(analyzer.external),
            "external_checkouts": sum(1 for u in analyzer.unresolved
                                      if u.scope == "external-checkout"),
            "olean_or_artifact_sites": sum(1 for u in analyzer.unresolved
                                           if u.scope == "runtime-oleans"),
            "contract": "runtime artifacts and tool binaries are bound by "
                        "runtime_sha256 / a recorded version, not by the input "
                        "map; they are not input-map entries",
        },
        "toolchain": {
            "declared_platform_inputs": platform,
            "dependency_lean_sources": [e["key"] for e in dep_toolchain],
            "lean_build_boundaries": sum(1 for b in closure["boundaries"]
                                         if b["kind"] == "lean-build"),
            "contract": "the Lean import graph / build / toolchain config are "
                        "toolchain consumption; this Python analyser does not "
                        "observe them and must not claim they are unused",
        },
    }

    return {
        "project": name,
        "project_dir": str(project_dir),
        "verifier": "tools/verify.py",
        "modules_analyzed": sorted(analyzer.modules),
        "pinned": {"input_sha256": len(input_pin),
                   "dependency_sha256": len(dep_pin)},
        "counts": {
            "pinned": len(input_pin),
            "read": len(read),
            "read_tcb": len([k for k in read if k not in exempt_keys]),
            "over_pinned": len(over),
            "under_pinned": len(under),
            "unclassified": len(unclassified),
            "incomplete_boundaries": len(closure["boundaries"]),
            "unresolved": len(analyzer.unresolved),
            "unresolved_repo": len(unresolved_repo),
            "exempt_observation": sum(1 for e in exempt
                                      if e["kind"] == "observation"),
            "exempt_external": sum(1 for e in exempt
                                   if e["kind"] == "external"),
        },
        "closure": closure,
        "categories": categories,
        "read_paths": sorted(read),
        # deprecated alias: "no consumer site discovered" -- never a usefulness
        # claim (see no_consumer_site_found / unclassified)
        "never_read": [o["key"] for o in over] + [u["key"] for u in unclassified],
        "no_consumer_site_found": [o["key"] for o in no_consumer],
        "over_pinned": over,
        "unclassified": unclassified,
        "under_pinned": under,
        "exempt_reads": exempt,
        "dep_covered_reads": dep_covered,
        "platform_inputs": platform,
        "unreached_functions": unreached,
        "dependency_map": dep_report,
        "unresolved": [
            {"expr": u.display, "reason": u.reason, "file": u.file,
             "line": u.line, "snippet": u.snippet, "fn": u.fn,
             "scope": u.scope}
            for u in analyzer.unresolved
        ],
        "writes": sorted(set(analyzer.writes)),
        "external_tools": sorted(analyzer.external),
        "admissions": admissions,
        "proposal": proposal,
    }


def build_proposal(project_dir: Path, input_pin: dict, read: dict,
                   platform: list, over: list, dep_covered: list,
                   closure: dict | None = None) -> dict:
    closure = closure or {"complete": True, "reasons": []}
    pin_mismatches = []
    for key, pinned in sorted(input_pin.items()):
        path = pin_target(key, project_dir)
        if not path.is_file():
            continue
        actual = sha256_file(path)
        if pinned != actual:
            pin_mismatches.append({"key": key, "pinned": pinned, "disk": actual})
    if not closure["complete"]:
        # Refuse to emit a safe-to-remove pin proposal: an untraversed
        # consumer boundary means "not found" is unclassified, not useless.
        return {
            "status": "WITHHELD",
            "withheld": True,
            "withheld_reason": WITHHELD_REASON,
            "withheld_because": closure.get("reasons", []),
            "proposed_pin": dict(sorted(input_pin.items())),
            "added": [],
            "removed": [],
            "pin_matches_disk": not pin_mismatches,
            "pin_disk_mismatches": pin_mismatches,
            "note": "read-only proposal; nothing was written to the repository. "
                    "No pin deletion is suggested while the closure is "
                    "incomplete: the existing pin rule is kept.",
        }
    proposed: dict[str, str] = {}
    mismatches = []
    dep_set = set(dep_covered)
    for key in sorted(set(read) | set(platform)):
        if classify(key, project_dir) != "input" or key in dep_set:
            continue
        path = pin_target(key, project_dir)
        if not path.is_file():
            continue
        actual = sha256_file(path)
        proposed[key] = actual
        if key in input_pin and input_pin[key] != actual:
            mismatches.append({"key": key, "pinned": input_pin[key],
                               "disk": actual})
    removed = [{"key": e["key"], "sha256": e["sha256"],
                "reason": "; ".join([e["reason"]] + e["evidence"][:2])}
               for e in over]
    return {
        "status": "PROPOSED",
        "withheld": False,
        "withheld_reason": None,
        "withheld_because": [],
        "proposed_pin": proposed,
        "added": [k for k in sorted(read) if k not in input_pin
                  and classify(k, project_dir) == "input" and k not in dep_set],
        "removed": removed,
        "pin_matches_disk": not mismatches,
        "pin_disk_mismatches": mismatches,
        "note": "read-only proposal; nothing was written to the repository",
    }


# --------------------------------------------------------------------------
# text output
# --------------------------------------------------------------------------

def render_text(report: dict) -> str:
    c = report["counts"]
    closure = report["closure"]
    lines = [
        f"== {report['project']}  ({report['project_dir']})",
        f"   verifier {report['verifier']}; modules: "
        + ", ".join(report["modules_analyzed"]),
        f"   pinned={c['pinned']}  read={c['read']} (tcb {c['read_tcb']})  "
        f"over={c['over_pinned']}  under={c['under_pinned']}  "
        f"unclassified={c['unclassified']}  "
        f"incomplete-boundaries={c['incomplete_boundaries']}  "
        f"unresolved={c['unresolved']} (repo-scoped {c['unresolved_repo']})  "
        f"exempt={c['exempt_observation']}obs/{c['exempt_external']}ext",
        f"   CLOSURE: {closure['status'].upper()}"
        + ("  -> " + "; ".join(closure["reasons"]) if closure["reasons"] else ""),
    ]
    if report["platform_inputs"]:
        lines.append("   declared toolchain inputs (implicit lake/lean reads): "
                     + ", ".join(report["platform_inputs"]))
    if closure["boundaries"]:
        lines.append("   INCOMPLETE consumer boundaries (not analysed here, so "
                     "they cannot be called unused):")
        for b in closure["boundaries"][:40]:
            where = f"{b['file']}:{b['line']}" if b["file"] else "<unknown>"
            lines.append(f"     ! [{b['category']}/{b['kind']}] {where} "
                         f"{b['detail']}")
        if len(closure["boundaries"]) > 40:
            lines.append(f"     ... {len(closure['boundaries']) - 40} more")
    if report["over_pinned"]:
        lines.append("   OVER-PINNED (pinned, never interpreted -> brittleness; "
                     "closure complete):")
        for entry in report["over_pinned"]:
            lines.append(f"     - {entry['key']}  [{entry['reason']}]")
            for evidence in entry["evidence"][:1]:
                lines.append(f"         witness: {evidence}")
    else:
        lines.append("   OVER-PINNED: none"
                     + (" (suppressed: no read site found is unclassified while "
                        "the closure is incomplete)" if not closure["complete"]
                        else ""))
    if report.get("unclassified"):
        lines.append("   UNCLASSIFIED (pinned, no consumer site found, closure "
                     "incomplete -> NOT evidence of uselessness):")
        for entry in report["unclassified"]:
            lines.append(f"     ? {entry['key']}  [{entry['reason']}]")
    if not closure["complete"]:
        lines.append(f"   PROPOSAL: {report['proposal']['status']} "
                     f"({closure['proposal_withheld_reason']}); no pin removal "
                     f"is suggested, the current pin is kept as-is")
    if report["under_pinned"]:
        lines.append("   UNDER-PINNED (interpreted, not pinned -> evidence gap):")
        for entry in report["under_pinned"]:
            site = entry["sites"][0]
            lines.append(f"     - {entry['key']}  ({site['kind']} at "
                         f"{site['file']}:{site['line']}) `{site['snippet']}`")
    else:
        lines.append("   UNDER-PINNED: none")
    for entry in report["exempt_reads"]:
        if entry["kind"] == "external":
            continue
        site = entry["sites"][0]
        lines.append(f"   read but exempt ({entry['kind']}): {entry['key']} "
                     f"[{site['file']}:{site['line']} {site['kind']}]")
    external_reads = [e for e in report["exempt_reads"]
                      if e["kind"] == "external"]
    if external_reads:
        lines.append(f"   read but exempt (external-checkout): "
                     f"{len(external_reads)} file(s) in dependency checkouts, "
                     f"bound by commit/config_sha256, not by the input map")
    dep = report.get("dependency_map") or {}
    if dep:
        lines.append(f"   dependency map: pinned={dep['pinned']} "
                     f"read={dep['read']} over={dep['over_pinned']} "
                     f"under={dep['under_pinned']} "
                     f"unclassified={len(dep.get('unclassified', []))} "
                     f"toolchain={len(dep.get('toolchain_consumed', []))} "
                     f"synthetic={len(dep['synthetic_keys'])}")
    cats = report.get("categories") or {}
    if cats:
        tools = ", ".join(cats["runtime"]["external_tools"]) or "none"
        lean_n = len(cats["toolchain"]["dependency_lean_sources"])
        lines.append(
            f"   categories: input {cats['input']['pinned']} pinned / "
            f"{cats['input']['consumed']} consumed / "
            f"{cats['input']['unclassified']} unclassified; "
            f"dependency {cats['dependency']['pinned']} pinned / "
            f"{cats['dependency']['consumed_python']} read by python / "
            f"{cats['dependency']['toolchain_consumed']} toolchain-consumed; "
            f"runtime tools: {tools}; toolchain lean sources: {lean_n}")
    if report["unresolved"]:
        lines.append("   UNRESOLVED read sites (coverage caveat):")
        for u in report["unresolved"]:
            lines.append(f"     ? [{u['scope']}] {u['file']}:{u['line']} "
                         f"`{u['snippet']}` -- {u['reason']}")
    if report.get("unreached_functions"):
        lines.append("   never reached from main() (no read sites can come from "
                     "them): " + ", ".join(report["unreached_functions"]))
    adm = report["admissions"]
    if adm:
        overfiles = [e for e in report["over_pinned"] if e["exists"]]
        if closure["complete"]:
            lines.append(f"   admissions: {adm.get('admitted')} "
                         f"(status {adm.get('status')}, pending {adm.get('pending')}); "
                         f"{len(overfiles)} pinned-but-unread file(s) can void them")
        else:
            lines.append(f"   admissions: {adm.get('admitted')} "
                         f"(status {adm.get('status')}, pending {adm.get('pending')}); "
                         f"{len(report['unclassified'])} pinned-but-unconsumed "
                         f"file(s) unclassified (closure incomplete: no removal "
                         f"claim)")
    return "\n".join(lines)


def render_proposal(report: dict) -> str:
    prop = report["proposal"]
    payload = {
        "project": report["project"],
        "status": prop.get("status"),
        "withheld": prop.get("withheld"),
        "withheld_reason": prop.get("withheld_reason"),
        "withheld_because": prop.get("withheld_because", []),
        "proposed_pin": prop["proposed_pin"],
        "added": prop["added"],
        "removed": prop["removed"],
        "pin_matches_disk": prop["pin_matches_disk"],
        "pin_disk_mismatches": prop["pin_disk_mismatches"],
        "closure_status": report["closure"]["status"],
        "note": prop["note"],
    }
    return json.dumps(payload, indent=2, ensure_ascii=False)


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------

def resolve_projects(selection: str, root: Path) -> list:
    names = (["root", "local-field", "bridge"] if selection in ("all", "")
             else [n.strip() for n in selection.split(",") if n.strip()])
    out = []
    for name in names:
        if name not in PROJECTS:
            raise SystemExit(f"error: unknown project {name!r}; choose from "
                             f"{', '.join(PROJECTS)} or 'all'")
        out.append((name, root / PROJECTS[name]))
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="tcb_manifest.py",
        description="Discover what each Lean verifier really reads, compare it "
                    "with verification/checked-inputs.json, and (optionally) "
                    "print a narrowed pin proposal. Read-only. No pin proposal "
                    "is emitted while the analysed closure is incomplete.",
        epilog="exit codes: 0 clean; 2 over/under-pinned findings on a complete "
               "closure; 3 at least one unresolved repo-scoped dynamic read "
               "site; 4 closure incomplete (unsupported consumer boundary, no "
               "removal proposal).")
    parser.add_argument("--project", default="all",
                        help="'root', 'local-field', 'bridge', a comma list, or "
                             "'all' (default)")
    parser.add_argument("--propose", action="store_true",
                        help="print the narrowed pin proposal {key: sha256} with "
                             "a reason for every removed key; writes nothing")
    parser.add_argument("--json", action="store_true",
                        help="print the full machine-readable report")
    parser.add_argument("--root", default=None,
                        help="repository root (default: parent of this file)")
    args = parser.parse_args(argv)

    # Reports contain the frozen phrase "closure incomplete — proposal withheld";
    # emit UTF-8 on every platform so a pipe, a file and a console agree.
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="backslashreplace")
    except (AttributeError, ValueError):   # pragma: no cover - StringIO / old io
        pass

    root = Path(args.root).resolve() if args.root else \
        Path(__file__).resolve().parent.parent
    reports = []
    for name, directory in resolve_projects(args.project, root):
        if not (directory / "tools" / "verify.py").is_file():
            raise SystemExit(f"error: {name}: no tools/verify.py under {directory}")
        reports.append(analyze_project(directory, name))

    if args.json:
        print(json.dumps(reports, indent=2, ensure_ascii=False))
    elif args.propose:
        print("\n".join(render_proposal(r) for r in reports))
    else:
        print("\n".join(render_text(r) for r in reports))

    findings = any(r["counts"]["over_pinned"] or r["counts"]["under_pinned"]
                   for r in reports)
    unresolved = any(r["counts"]["unresolved_repo"] for r in reports)
    incomplete = any(not r["closure"]["complete"] for r in reports)
    if unresolved:
        return 3
    if incomplete:
        # Never exit 0 while a consumer boundary is untraversed: "no read site
        # found" would otherwise read as a clean, complete closure.
        return 4
    if findings:
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
