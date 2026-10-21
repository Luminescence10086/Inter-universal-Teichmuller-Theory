/-
Library root for the isolated M2 candidate project.

It only re-exports the single entry file `Candidates/OrbitQuotient.lean` so that
`lake build` can produce the oleans needed by `Candidates/Axioms.lean`.
No mathematics is stated here.
-/

import Candidates.OrbitQuotient
