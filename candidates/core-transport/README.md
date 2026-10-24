# CoreTransport — frozen arithmetic boundary

This candidate transports the literal logarithm series under a continuous field isomorphism and independently transports multiplication, root-of-unity orbits and principal regions. The concrete arrow is Mathlib's `Padic.adicCompletionEquiv ℤ p`, from Cauchy-completion p-adics to the height-one valuation completion of the rationals. It is not a nontrivial Galois automorphism or an IUT Ind1/Ism realization.

`CoreTransport.Basic.localLog_natural` commutes `tsum` using a continuous additive equivalence with continuous inverse. Its equality is valid for Lean's totalized series, including the default value in nonsummable cases. `principal_unit_iff` separately proves preservation of the genuine norm-radius domain, and `logImage_transport` transports the literal series image of that domain. Neither theorem alone proves arithmetic summability.

Work was frozen at the user's requested pivot to existing GitHub formalizations. The explicit equality to `PadicLogVolume.padicLog`, transfer of the new port's convergence theorem, and a nontrivial power-map or Galois instance have NOT been completed. No claim is made to have a certified log-image lattice, a kernel description or RI03–RI05 realization. The actual integer-ring commuting square keeps the integer subring and the same field arrow explicit. The stronger integer-ring iff and its principal-region instance failed on an integer-algebra instance mismatch; their goals and attempted proofs are retained only in Unfinished.md, excluded from Lean modules and exports.

External-source audit: `../../reviews/core-round/transport/source-seam.md`. It quotes the precise enlarged `factorAut`, `tensorAut`, analytic `theta_admissible`, original `RHSData.thetaPilot` field, and `Wall` eta-comparison hypothesis, including the zero-gap premise required for the repository's stronger comparison equivalence.

Build uses Lean 4.34.0-rc2 and the existing local Mathlib, transitively through `../core-log`. `lake update` generated a manifest but its optional Mathlib cache hook failed due existing path-based dependency pins; subsequent `lake env lean` uses the installed local oleans. Validation is direct with `-DwarningAsError=true`; no test-hiding linter suppression, no new axioms, no sorry/admit/native_decide.

