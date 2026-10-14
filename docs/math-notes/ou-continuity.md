# Strong OU continuity and ambient weak-operator continuity

## Verified scope

The native Ornstein–Uhlenbeck maps already act on the actual norm-closed algebra
of real fields associated to any orthonormal family in a complete complex
Hilbert space. No spanning or countability assumption is added here.

`OrnsteinUhlenbeckContinuityDense.lean` proves
`familyOUTime_joint_continuous` and `familyOUTime_strong_continuous` on all
nonnegative real times, including zero. Joint continuity means continuity of
`(t,T) ↦ P_t(T)` in the native C-star norm. This does not assert operator-norm
continuity of the family of bounded endomorphisms `t ↦ P_t`.

The proof starts with the actual Wick eigenvalue formula. The vectors with
continuous time orbits form a complex submodule. This submodule contains every
Wick polynomial, hence is dense in the actual closed algebra. The uniform
norm-contraction estimate extends joint continuity from these dense continuous
orbits to all native elements.

`OrnsteinUhlenbeckContinuityHilbert.lean` proves
`degreeDamping_joint_continuous` and `degreeDamping_strong_continuous` on the
whole completed infinite tensor Hilbert sum. Every single-degree vector has a
continuous orbit; the convergent sum of all degree embeddings supplies density.
The same uniform contraction argument applies. Restriction to the genuine
complete cyclic Hilbert subspace gives `familyOUL2_joint_continuous` and
`familyOUL2_strong_continuous`. For a nonspanning orthonormal family this cyclic
space is retained as a subspace; it is not identified with all ambient Fock
space.

## Actual ambient WOT maps

`SecondQuantizationWOTCompression.lean` uses mathlib's genuine
`ContinuousLinearMapWOT` topology. For any bounded map `W : E →L[ℂ] F`,
`boundedCompressionWOT_continuous` proves continuity of the actual sandwich
`T ↦ W.adjoint ∘ T ∘ W`. Its coefficient identity is

`⟪y, W.adjoint (T (W x))⟫ = ⟪W y, T (W x)⟫`.

For a Hilbert unitary `U : E ≃ₗᵢ[ℂ] F`,
`unitaryConjugationWOT_continuous` proves continuity of actual unitary
conjugation. Its coefficient identity pulls back both vectors through `U.symm`.
The proof uses the coefficient characterization of WOT continuity directly.

`secondQuantizationCompressionWOT_continuous` specializes the sandwich to the
actual arbitrary one-particle isometry's completed-tensor second quantization.
The `_toCLM` theorem identifies it definitionally with the previously verified
`secondQuantizationCompression`. The corresponding unitary-conjugation theorem
uses the actual full-space unitary `secondQuantization U` and its existing
`conjStarAlgEquiv`. No assertion is made that an arbitrary complex one-particle
unitary preserves a fixed chosen real-field algebra.

## Verification and implementation decisions

The focused modules compiled under the common build lock. Principal statements
were audited transitively with `#print axioms`; they use only `propext`,
`Classical.choice`, and `Quot.sound`. The proof-source integrity guard passed.
Published mathematical checkpoints are `b57ec04` (native strong continuity),
`6d173ac` (complete tensor and cyclic Hilbert continuity), and `d4f9e1f`
(actual ambient WOT compression and conjugation).

Only the pinned targeted cache for
`Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology` was hydrated for the
WOT module. No toolchain or dependency revision changed.

A direct application of product-continuity composition to the large native
algebra expression caused an elaboration timeout. A typed generic
`continuous_orbit_of_joint` helper avoids unfolding those instances. This changes
neither the theorem nor the proof resource limits.

## Remaining mathematical obligations

Ambient WOT continuity is not a normal extension theorem for the native OU
self-map. The included native algebra embedding is currently a norm-isometric
star homomorphism. Its WOT continuity on norm-bounded sets, or an explicit normal amplification
representation, still needs a separate proof. Infinite amplification need not
be globally WOT-continuous on unbounded nets; normality requires the correct
bounded or ultraweak interface and a proved extension argument. A norm-isometric homomorphism
alone does not establish this bridge.

Pinned mathlib provides the concrete weak operator topology and its coefficient
calculus, but no ready bicommutant theorem, Kaplansky density theorem, or
ultraweak/predual normal-map package was located. Extension to a von Neumann
closure therefore requires explicit representation and closure arguments.
No normal OU extension, L1 extension, hypercontractivity, logarithmic Sobolev
inequality, or entropy conclusion follows from this checkpoint alone.
