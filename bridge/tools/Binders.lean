import Lean
import IUTBridge

/-! Infrastructure only. **Hypothesis audit.**

For every catalog target this reports the *syntactic* binder telescope of the
elaborated type: binder name, printed type, whether the type is a `Prop`, and
whether the binder is an instance-implicit typeclass argument.

The peeling is deliberately non-reducing. `forallTelescopeReducing` would unfold
`Not P` into `P → False` and thereby turn a *negated conclusion* into an extra
hypothesis; that would make every `¬`-shaped theorem look conditional. Here a
`Not` stays a conclusion.

The verifier then requires that every explicit, non-typeclass `Prop` binder is
declared in `tools/catalog.json` under `hypotheses`. A theorem that quietly
acquires an extra premise therefore fails verification instead of being counted
as unconditional progress.
-/

open Lean Meta

/-- Peel the syntactic `forall` telescope of `ty`, substituting through `let`
binders but never reducing definitions such as `Not`. Bound variables are
replaced by local free variables one binder at a time, so that each binder type
can be pretty-printed in its own context. -/
partial def peelBinders (ty : Expr) : MetaM (Array Json) := do
  let rec go (ty : Expr) (acc : Array Json) : MetaM (Array Json) := do
    match ty with
    | .forallE n t b bi =>
        withLocalDeclD n t fun x => do
          let isProp ← Meta.isProp t
          let tyStr := (← Meta.ppExpr t).pretty
          go (b.instantiate1 x) (acc.push <| Json.mkObj [
            ("name", toJson n.toString),
            ("type", toJson tyStr),
            ("isProp", toJson isProp),
            ("isInstance", toJson (bi == BinderInfo.instImplicit)),
            ("isExplicit", toJson (bi == BinderInfo.default))])
    | .letE _ _ v b _ => go (b.instantiate1 v) acc
    | _ => pure acc
  go ty #[]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let catalogJson ← IO.FS.readFile "tools/catalog.json"
  let parsed ← match Json.parse catalogJson with
    | .ok j => pure j
    | .error e => throwError s!"bad tools/catalog.json: {e}"
  let entries : Array Json := match parsed with
    | .arr a => a
    | _ => #[]
  if entries.size == 0 then throwError "tools/catalog.json has no entries"
  let mut rows : Array Json := #[]
  for entry in entries do
    let idJson ← match entry.getObjVal? "id" with
      | .ok v => pure v
      | .error _ => throwError "catalog entry without id"
    let id := match idJson with
      | .str s => s
      | _ => ""
    if id.isEmpty then throwError "catalog entry id is not a nonempty string"
    let some ci := env.find? id.toName | throwError s!"catalog target not found: {id}"
    let isThm := match ci with
      | .thmInfo _ => true
      | _ => false
    unless isThm do throwError s!"catalog target is not a theorem: {id}"
    let binders ← liftTermElabM (peelBinders ci.type)
    rows := rows.push <| Json.mkObj [("id", toJson id), ("binders", toJson binders)]
  logInfo (Json.compress (toJson rows))
