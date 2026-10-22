/-
# Library root module for the `core-transport` package

**This file is a structural fix, not mathematics.** It declares nothing: no theorem, no
definition, no instance, no axiom. It only re-exports two modules that already existed.

## Why it has to exist

`lakefile.lean` declares `lean_lib CoreTransport`, and Lake resolves a library's root to the
module named after it, i.e. `CoreTransport.lean` in the package directory. That file was absent,
so `lake build CoreTransport` failed with:

    error: no such file or directory
      file: .../candidates/core-transport/CoreTransport.lean

Consequences that made this a *verification* problem rather than a cosmetic one:

* the whole-library build could not run at all, so `lake build` reported "some modules have bad
  imports or could not be read" for a package whose individual files compile cleanly;
* the VS Code Lean 4 extension could not obtain a build plan for imports and therefore refused to
  elaborate any file in the package, reporting instead its stale-imports guard
  (`Imports are out of date and must be rebuilt; use the "Restart File" command`). That single
  editor diagnostic is what blocked the editor check.

## Authorisation and scope, stated plainly

Task T3 of `handoffs/core-support-2026-10-22.md` permits exactly one new Lean source,
`DelegatedLogBridge.lean`. **This file is outside that permission.** It was authorised explicitly
by the user on 2026-10-23 ("允许，但是要标注清楚") and is marked here so that no later reader can
mistake it for part of the delegated deliverable or for new formalisation work.

It does not change any existing file, does not touch `DelegatedLogBridge.lean`, introduces no
`sorry`/`admit`/`axiom`, and adds no mathematical content of any kind.
-/
import CoreTransport.Basic
import CoreTransport.Completion
