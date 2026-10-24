# Outer approximation order bridge — candidate

This file checks order/quantifier bookkeeping; it supplies no IUT realization and
claims no mathematical novelty. Lean 4.34.0-rc2, local cached Mathlib at
85e3a25e006c35636f0e53b0e9296caca2685bc0.

`OrderBridge.lean` proves:

1. A lower bound on an infimum is a lower bound on **every** outer approximant.
2. If for every epsilon one actual allowed witness has all its outer
   approximants above q-epsilon, and that witness's infimum obeys an independent
   upper bound b, then q <= b.
3. A two-approximant counterexample rules out replacing **every** by **some**.

The same witness is fixed before quantifying over all its approximants. It may
depend on epsilon. Thus the scalar bound does not demand compactness or an exact
attaining witness. EReal is used so empty/unbounded infimum boundary cases are
not silently replaced by the totalized real infimum. No conversion of IUT's
formal quotient into this indexed EReal family has been proved.

This candidate reuses the existing core-transport environment without changing
its Lake configuration. From `../core-transport` run:

```powershell
lake env lean -DwarningAsError=true ../core-order-bridge/OrderBridge.lean
```

Actual final stdout/stderr and exit metadata are under
`reviews/core-compatibility-2026-10-23/order/`. Three axiom outputs contain only
propext, Classical.choice, Quot.sound. CLI checked; actual VS Code admission
pending; no fact-tree mutation.
