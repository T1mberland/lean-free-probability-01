# The whole double commutant acts on the original family cyclic Hilbert space

The cyclic Hilbert space remains exactly the previously constructed
`familyCyclicSpace e`: the complete norm closure of vacuum vectors of the
original prescribed-family norm-closed star algebra. It is not replaced by all
ambient Fock space, and the field family need not span the one-particle space.

## Verified milestones

- `8d66fb1`, `OrnsteinUhlenbeckVonNeumannCyclicProjection.lean`:
  each given self-adjoint field preserves the ORIGINAL complete cyclic space,
  using actual multiplication in its original norm-closed algebra and norm
  closure continuity. The genuine orthogonal projection onto this space
  commutes with every given field, lies in their literal commutant, and fixes
  the actual tensor vacuum. The field family is arbitrary; no orthonormality,
  spanning, countability, or nontriviality assumption enters this step.
- `df2fe00`, `OrnsteinUhlenbeckVonNeumannCyclicVector.lean`:
  every actual operator in `tensorFamilyDoubleAlgebra e` commutes with that
  projection. Consequently EVERY whole-double-commutant vacuum vector `TΩ`
  lies in the SAME original `familyCyclicSpace e`, with no orthonormality
  assumption or polynomial-density assumption on the double commutant.
  `ouVonNeumannCyclicVector` is genuine bounded evaluation with this complete
  cyclic codomain. The original norm-closed family algebra is included in the
  literal double commutant, so the whole-algebra evaluation has dense range
  in that same Hilbert space. For an orthonormal family it is injective by
  genuine faithful vacuum separation.
  `familyOUL2_ouVonNeumannCyclicVector` proves the existing complete cyclic OU
  contraction agrees on EVERY whole-double-commutant vacuum vector.
- `c0bb616`, `OrnsteinUhlenbeckVonNeumannCyclicRepresentation.lean`:
  every actual double-commutant operator preserves the original cyclic space,
  not only its vacuum. Restriction defines the actual unital star
  representation `ouVonNeumannCyclicAction` on that complete Hilbert space.
  It implements left multiplication on every whole-algebra vacuum vector.
  For an orthonormal family, actual vacuum separation makes this star
  representation injective; the genuine injective C-star homomorphism theorem
  proves full operator-norm preservation.

## Actual reducing-projection argument

Let `P` be the genuine orthogonal projection onto the original cyclic closure.
Self-adjointness and invariance of each given field prove `P` commutes with that
field. Thus `P` belongs to the literal field commutant. Every operator `T` in
the field double commutant commutes with `P`. Since `PΩ=Ω`,

`P(TΩ)=T(PΩ)=TΩ`.

The same argument with any vector already in the cyclic space establishes
whole-space invariance and the actual restricted star representation. No
bicommutant/WOT-closure equivalence, Kaplansky theorem, or spanning-family
shortcut is used.

## Verification and precise scope

All three final focused builds completed with exit code zero under the common
build lock. Twenty-one principal direct axiom audits completed with exit code
zero and used only `propext`, `Classical.choice`, and `Quot.sound`. Proof-source
integrity and whitespace diff checks passed. Each atomic mathematical commit
was pushed successfully before subsequent work. All frozen prior tensor,
cyclic L2, intrinsic OU, number-operator and generator sources were preserved.

Projection and cyclic action are actual operators on the genuine complete
Hilbert spaces. ON assumptions enter only the faithful/injective or
norm-preserving assertions and the existing named `familyOUL2` interface;
arbitrary-family vacuum-range membership and restricted star action have no
such assumption.

The dense actual vacuum representation, genuine state inner-product identity,
and same-space complete cyclic contraction provide the concrete family-correct
L2 bridge. An explicit unitary to a separately constructed abstract GNS
completion is not asserted here. Neither that star representation's image being
a von Neumann algebra nor a normal-representation interface is inferred from
its injectivity or norm isometry.

## Remaining independent obligations

Operator-domain and generator transfer to a separately specified complete
whole-algebra GNS/L2 package, positive-time family-correct regularization bounds,
a distinct closed quadratic-form package, intrinsic L1 extension,
hypercontractivity, logarithmic Sobolev inequalities, and entropy remain
separate obligations. The previously verified ambient strong generator acts on
actual full Fock vectors; applying it to the proper family cyclic space requires
its correct invariant-domain interface rather than silently identifying that
cyclic space with all ambient Fock space.
