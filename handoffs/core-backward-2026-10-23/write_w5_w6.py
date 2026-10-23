"""Write the W5 and W6 delivery packages."""
import hashlib
import io
import json
import time
from pathlib import Path

ROOT = Path(r'D:\Inter-universal Teichmüller Theory')
BASE = ROOT / 'handoffs/core-backward-2026-10-23'

DOC_W5 = """# W5 — gate record

Deliverable: `candidates/core-transport/NormalizationAlignment.lean`
sha256 `03b6e50289e4150b8ef98537deab952b14f5e80b0d8ccdc850a8be8ee56b2412`, 406 lines, 31 declarations,
31/31 axiom reports.

## What it formalises

The H3 alignment obligation (see `research/core-backward-2026-10-23/h3-prerequisites.md`): the source's
procession normalization is an **average over the label orbit** `j in F_l^star`, while (xi-d) indexes by
`|F_l|` with the label `0` identified with `langle F_l^star rangle` (IUT II Cor 4.10(i)). The algebraic
content of that identification is: *for an invariant reading, averaging over the orbit equals the value at
the label*.

```
theorem average_eq_value_of_invariant (hf : Invariant f) (g : G) : orbitAverage f = f g
theorem alignment (hf : Invariant f) : orbitAverage f = f 1
```

## Gates

- CLI: `lake env lean -DwarningAsError=true NormalizationAlignment.lean` — exit 0, stderr 0 bytes.
  Independent strict re-check: **PASS** — 31 declarations, 0 errors, 0 warnings, 31 axiom reports,
  axioms only `{propext, Classical.choice, Quot.sound}`, no forbidden terms.
- Editor: trusted workspace, Lean 4 active — **0 errors, 0 warnings**, information entries present.
  Capture: `editor/vscode-observation-tree-2.txt`.
- Infoview: not attempted (the three gates for this batch are CLI, axiom whitelist, editor zero
  diagnostics).

## Anti-degeneracy

`LabelGroup = Equiv.Perm (Fin 2)`; a reading with values `5` at `1` and `7` at `swapLabels`; the orbit
average is `6 = (5+7)/2`, the value at the label is `5`, so `6 != 5`, and `not Invariant` is proved — the
hypothesis really fails. Non-vacuity: `invariant_const`, `orbitAverage_const`.

The file also discloses `invariant_iff_const` (on the self-action carrier, invariance *is* constancy)
rather than hiding it.

## What it does not say

It does not prove that (xi-d)'s `|F_l|` index *is* the procession average. It proves that for an invariant
reading, orbit-averaging and value-at-label coincide, so group-indexing and label-indexing agree at that
level; the source alignment remains a **definition alignment**, not a theorem of this file. Nothing here
touches Θ-links, `Ism`, log-volumes or Cor 3.12. Core GAP stays OPEN.
"""

DOC_W6 = """# W6 — gate record

Deliverable: `candidates/core-transport/ReadingFactorization.lean`
sha256 `6a756a88d57eed9892e749eb0c8abea75c1aa289bd0556f44c3e9f8e5fb2716d`, 881 lines,
83 declarations, 83/83 axiom reports.

## What it formalises

W4 showed the reading is *constant on a compatible chain*. W6 shows it **descends to the quotient**:

- `SameObjectStep c a b` = the recorded transition really transports the presentation; `SameObject` is its
  `ReflTransGen` closure (the closure is needed: no field relates `unit a b` to `unit b a`; on a compatible
  chain it is redundant, `sameObjectStep_direct`).
- `descendedReading := Quotient.lift (reading c) sameObject_reading_eq`, with the lift obligation proved
  per step (`reading_eq_of_transport`), plus `descendedReading_unique`.
- `descendedReading_mk : descendedReading c hc (Quotient.mk _ i) = c.reading i`.

## Gates

- CLI: exit 0, stderr 0 bytes; independent strict re-check **PASS** — 83 declarations, 0 errors,
  0 warnings, 83 axiom reports, axioms only `{propext, Classical.choice, Quot.sound}`.
- Editor: **0 errors, 0 warnings**; capture in `editor/vscode-observation-tree-2.txt`.
- Infoview: not attempted.

## Anti-degeneracy

On `chainBroken` (units `0->1 = 4`, `1->2 = 4`, `0->2 = 64`): `4*64 = 256 != 64` kills the one-step `0~2`
edge, yet `16*4 = 64` keeps `i1 ~ i2` while the readings are `localLog 4` and `0`. Hence **no
factorization through the quotient at all** (`no_factorization_on_broken`). The compatible twin has one
edge, all readings equal, `descendedReading` constant.

The builder states the honest limitation in the docstring: `step_input` is a field, so `SameObject` is
total and the quotient is a subsingleton on every chain; the weight rests on constancy.

## Why quotient rather than constancy

Constancy compares values along one chain; `Quotient.lift` produces the unique function *on the
isomorphism classes* — the object-level statement — and its failure becomes "no factorization through the
quotient", which is exactly the orbit-shaped obligation of `h1-coricity.md`. Nothing here touches IUT's
localization data, log-volumes, Θ-links or Cor 3.12. Core GAP stays OPEN.
"""


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def package(task, src, doc, outputs_extra, completed, unresolved):
    check = json.load(io.open(BASE / task / 'check.json', encoding='utf-8'))
    editor_tree = BASE / task / 'editor/vscode-observation-tree-2.txt'
    editor_text = editor_tree.read_text(encoding='utf-8')
    # the document has to exist before its own hash can be recorded
    (BASE / task / 'editor-check.md').write_text(doc, encoding='utf-8')
    d = {
        'task_id': task,
        'status': 'CLI_CHECKED_EDITOR_CHECKED',
        'vocabulary_note': 'the batch vocabulary has no value for a Lean task verified in both planes',
        'started_at': time.strftime('%Y-%m-%dT%H:%M:%S%z'),
        'inputs': [
            {'path': 'research/core-backward-2026-10-23/h3-prerequisites.md',
             'sha256': sha(ROOT / 'research/core-backward-2026-10-23/h3-prerequisites.md')},
            {'path': 'candidates/core-transport/CoreTransport/Basic.lean',
             'sha256': sha(ROOT / 'candidates/core-transport/CoreTransport/Basic.lean')},
        ],
        'outputs': [
            {'path': str(src.relative_to(ROOT)).replace('\\', '/'), 'sha256': sha(src)},
            {'path': str((BASE / task / 'check.json').relative_to(ROOT)).replace('\\', '/'),
             'sha256': sha(BASE / task / 'check.json')},
            {'path': str((BASE / task / 'editor-check.md').relative_to(ROOT)).replace('\\', '/'),
             'sha256': sha(BASE / task / 'editor-check.md')},
            {'path': str(editor_tree.relative_to(ROOT)).replace('\\', '/'), 'sha256': sha(editor_tree)},
        ] + outputs_extra,
        'gates': {
            'cli': {'exit': 0, 'stderr_bytes': 0, 'diagnostics': check['counts'],
                    'theorems_with_axiom_report': len(check['axioms']) + len(check['axiom_free']),
                    'axioms': sorted({a for v in check['axioms'].values() for a in v}),
                    'forbidden_terms': len(check['forbidden']), 'source_sha256': sha(src)},
            'editor': {'product': 'Visual Studio Code 1.143.0',
                       'lean_extension': 'leanprover.lean4-0.0.240',
                       'errors': editor_text.count('ControlType.TreeItem | \u9519\u8BEF:'),
                       'warnings': editor_text.count('ControlType.TreeItem | \u8B66\u544A:')},
            'infoview': {'attempted': False,
                         'reason': 'not required by the three gates for this batch'},
        },
        'completed': completed, 'unresolved': unresolved,
        'core_gap': 'OPEN', 'lean_run': True, 'editor_run': True, 'fact_tree_admitted': False,
    }
    (BASE / task / 'editor-check.md').write_text(doc, encoding='utf-8')
    (BASE / task / 'delivery.json').write_text(
        json.dumps(d, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    return d


w5 = package(
    'W5', ROOT / 'candidates/core-transport/NormalizationAlignment.lean', DOC_W5,
    [{'path': 'handoffs/core-backward-2026-10-23/W5/README.md', 'sha256': sha(BASE / 'W5/README.md')}],
    ['average_eq_value_of_invariant: for an invariant reading, the orbit average equals the value at any '
     'point of the orbit',
     'alignment: the special case at the label 1, which is the algebraic content of 0 <-> <F_l^star>',
     'anti-degeneracy computed (6 against 5) with an explicit proof that invariance fails'],
    ['this is the shape, not the source statement: it does not prove (xi-d) uses the procession average',
     'no Theta-link, Ism, log-volume or Cor 3.12 appears'])

w6 = package(
    'W6', ROOT / 'candidates/core-transport/ReadingFactorization.lean', DOC_W6,
    [{'path': 'handoffs/core-backward-2026-10-23/W6/README.md', 'sha256': sha(BASE / 'W6/README.md')}],
    ['SameObject is the ReflTransGen closure of the transport relation; on a compatible chain it is '
     'redundant (sameObjectStep_direct)',
     'descendedReading via Quotient.lift, with the constancy obligation proved per step',
     'descendedReading_mk: the descended function computes the original reading',
     'anti-degeneracy: on a broken chain no factorization through the quotient exists at all'],
    ['Fin k is an index set, not places; transitions are multiplication by powers of 4',
     'step_input is a field, so the quotient is a subsingleton on every chain; the weight rests on constancy',
     'nothing here touches Ibar-fQ1/Ibar-fQ2, log-volumes, Theta-links or Cor 3.12'])

for d in (w5, w6):
    print(d['task_id'], d['status'], d['gates']['cli']['diagnostics'],
          'editor', d['gates']['editor']['errors'], d['gates']['editor']['warnings'],
          'axioms', d['gates']['cli']['axioms'])
