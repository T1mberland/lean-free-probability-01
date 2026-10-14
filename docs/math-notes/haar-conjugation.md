# Abstract Haar-unitary conjugation

This verified milestone supplies the abstract part of Goal 9, not its finite
random-matrix integration or asymptotic results. Worktree branch:
`feat/haar-conjugation`, from checked main `272452c`.

## Published source milestones

- `95feb08`, `Algebraic/HaarUnitary.lean`:
  `unitaryPower u j` takes integer powers in the ACTUAL unitary group and then
  embeds into the ambient ring. It does not require a division ring, ambient
  integer powers, or an inverse-closed arbitrary subalgebra.
  `IsHaarUnitary` requires expectation zero for every nonzero integer power.
  `IsHaarUnitary.expectation_starWord` proves the COMPLETE star-word law: the
  moment is one precisely when the signed exponent is zero, otherwise zero.
  Every integer power belongs to the entire actual generated star algebra.
- `3a42f2d`, `Algebraic/HaarConjugationWords.lean`:
  `expectation_haarConjugate` proves expectation preservation on the ENTIRE
  base algebra from its freeness with the entire Haar-generated star algebra.
  `expectation_haarConjugates_prod_eq_zero` proves vanishing of complete
  alternating centered products of integer conjugates.
- `2ff26dd`, `Algebraic/HaarConjugation.lean`:
  `freelyIndependent_haarConjugatedAlgebras` proves that the entire actual
  subalgebra images B_j = u^j B u^(-j), indexed by ALL integers, form a freely
  independent family. Arbitrary injective selections are free as well.
  `sameDistribution_haarConjugate` preserves every joint moment of a family
  from B; `sameStarDistribution_haarConjugate` preserves every joint star
  moment when the supplied original algebra is star closed.

## Generality and proof

The ambient setup is a unital algebraic probability functional over a field with
compatible star structures. There are NO trace, positivity, completeness or
continuity premises. Full freeness of B and the whole Haar-generated algebra is
an explicit mathematical hypothesis; it is not replaced by independence of a
few moments. The copies are actual full algebra images under
`Unitary.conjStarAlgAut`, not a generator-only free-family surrogate.

The expanded product is
u^j0 b0 u^(j1-j0) b1 ... u^(jr-j(r-1)) br u^(-jr).
All interior differences are nonzero because ORIGINAL ADJACENT labels differ.
Nonadjacent repeated labels are permitted. Each retained power is centered by
Haar moments. A peripheral zero power is omitted, avoiding an uncentered identity
letter. The resulting genuine word alternates between the original two free
algebras and its product telescopes exactly. No cyclic rotation or endpoint
merging is needed, so no trace assumption is added. An initial attempted cyclic
proof route would have imposed an avoidable trace hypothesis and was discarded.

## Verification and remaining obligations

All three focused modules compile warning free under the common lock. Important
results passed transitive audits using only standard Lean logical foundations.
The source-integrity guard passed before each atomic commit; diffs were reviewed
and every commit was pushed immediately. Failed elaborations concerned subtype
integer-power cast spelling, map simplification, explicit function composition,
star-map rewriting, and induction-argument order. Statements were preserved.

The mathematical abstract conjugation theorem is proved. Universal construction
of a freely independent Haar unitary with arbitrary supplied algebras is separate.
General Haar orthogonal integration/pairing estimates and joint asymptotic freeness
of independent Haar matrices remain unproved here. Expected normalized traces,
convergence in probability, almost-sure convergence, and strong convergence must
retain distinct hypotheses and conclusions; none is claimed by this milestone.
Goal certification, central imports, integration checks and ledgers are coordinator-owned.
