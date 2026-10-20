# claim_index — claim → theorem traceability

**Analogy.** *Doctest / literate testing*: prose is not trusted, executable references are —
here one "runnable" assertion is "this sentence names a theorem the verifier exported".
*SBOM provenance*: every claim about the artifact must carry a component pointer into a
manifest produced by the build, not by the author's memory. *Explicit waivers*: as with a
scanner baseline, an unanchored claim may be declared `<!-- narrative -->`, and declared ones
are **listed**, never silently dropped.
**Why anchors must be fact-tree ids, not "a theorem name exists".** A name-shaped token is
free to type — that is how the four documented defects were written (`"cost formula"`,
`"strictly increasing"`, a `slot-mixing` generalisation, `"cannot be formalized"`). A
fact-tree id is emitted by `verify.py` from elaborated Lean, so requiring it makes the claim
*provenance-relative*: the question becomes "which build output says this?", answerable by a
machine. It also buys the cheaper second check — **dangling**: when a theorem is renamed or an
id mistyped, the doc keeps pointing at nothing and the index sees it (exit 1). Today: 0
dangling, so no stale anchors in the indexed set.

**What it counts.** claims = anchored + narrative + unanchored + dangling (disjoint;
precedence dangling > narrative > anchored > unanchored, because a waiver must not launder a
stale reference). Anchoring is checked **within the claim** (one sentence or one table row),
so an anchor cannot live three paragraphs away.

**Limits — read this before trusting a green run.**
1. **It cannot judge whether the wording is faithful to the statement.** That is the whole
   defect class and the index does not touch it. A sentence carrying a real id still counts as
   anchored if it says *strictly increasing* while the theorem is antitone, calls a set-image
   identity a *volume cost formula*, or generalises to slot-mixing actions no theorem covers.
   Getting the id right is necessary, not sufficient.
2. **A human or LLM reviewer must still** open the node's `statement` (with `hypotheses`,
   `axioms`, `scope`) and check direction/order (monotone vs antitone), quantifier scope,
   whether the claim is stronger than the statement, whether `admitted` is being sold as
   *proved*, and whether the cited theorem is doing the work or is a decorative neighbour.
   The index says "points somewhere real"; a reviewer says "says the right thing".
3. **Recall is lexical** — the trigger lists at the top of `claim_index.py`. Defects phrased
   without a trigger (`"is a volume cost formula"`, `"slot-mixing actions commute"`) are
   invisible to it; those were found by review and will be again. 399 is a floor, not a
   measure of faithfulness. Likewise, not every machine fact is a theorem fact: toolchain
   pins and file counts have no fact-tree home, so they are unanchored or narrative by design.
5. **Deliberately strict**: the fully-qualified id is required, so a table whose namespace is
   declared once in the intro paragraph (`round4-results.md`, 14 rows) reads as unanchored —
   convention debt, not misstatement; 75 such claims are fixed by `--fix-hints` (suffix
   match, then difflib).
