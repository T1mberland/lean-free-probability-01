# Intrinsic completely positive OU maps

The source and target are the actual norm-complete C-star algebra
`tensorFamilyDoubleAlgebra e`. Its carrier is proved equal to the literal double
centralizer of the given real field generators on `TensorFullFock H`; it is the
star algebra underlying the bundled `tensorFamilyVonNeumannAlgebra e`.
The prescribed family `e : I → H` is arbitrary. No orthonormality, spanning,
countability, or nontriviality assumption enters the following construction.

## Verified milestones

- `9f638ea`: `OrnsteinUhlenbeckVonNeumannIntrinsicCP.lean` constructs
  `ouVonNeumannCP e r s hrs` for real parameters with `r²+s²=1`. It is the exact
  restriction of `ouDoubleCommutantRawCP`, whose literal double-commutant range
  was already verified. It preserves the unit, contracts the operator norm,
  and preserves the actual positive normalized vacuum state.
- `64ee419`: `OrnsteinUhlenbeckVonNeumannIntrinsicTime.lean` specializes to
  `r=exp(-t)`, `s=sqrt(1-r²)` for `t≥0`. `ouVonNeumannTimeCP_zero` proves the
  identity at time zero on every element of the whole double commutant.
  `ouVonNeumannTimeContinuous` is a genuine bounded linear realization on this
  complete C-star algebra, with operator norm at most one.
- `be042e3`: `OrnsteinUhlenbeckVonNeumannIntrinsicWOT.lean` represents the same
  intrinsic CP map on the intersection of the concrete double commutant with
  each uniform operator norm ball. This space carries the actual subspace
  topology from ambient WOT. Exact agreement with the CP map and continuity
  as a self-map of that norm ball are proved.

## Actual matrix positivity

The intrinsic order is the canonical C-star spectral order. Complete positivity
is proved at every canonical finite `CStarMatrix` level. The actual subtype
star homomorphism induces an injective matrix star homomorphism; its
`map_le_map_iff` reflects the full canonical positive cone. Intrinsic positive
matrices are mapped to positive ambient matrices, the genuine ambient CP map
preserves positivity, and reflection returns positivity in the intrinsic
codomain. No Gram-only positivity premise or assumed positive-cone reflection
is introduced.

## Verification and elaboration decisions

All three final focused builds completed with exit code zero under the common
build lock. Sixteen principal direct axiom audits completed with exit code
zero and used only `propext`, `Classical.choice`, and `Quot.sound`. Proof-source
integrity and whitespace diff checks passed. Each atomic source commit was
pushed successfully before further development.

Explicit ambient Hilbert-space type parameters and subtype coercions avoid
elaboration unfolding the chosen basis while inferring an operator type. No
resource-limit increase or alteration of the frozen ambient proofs was needed.

## Remaining mathematical obligations

This checkpoint proves intrinsic unital CP contractions and concrete bounded-WOT
continuity. It does not prove the additive semigroup law or preservation of
bounded increasing positive suprema. Continuity is restricted to uniform norm
balls; global WOT continuity on unbounded nets is not asserted.

For a prescribed orthonormal family, a promising separate composition proof
is the identity on all vacuum vectors

`P_t(T) Ω = D_t(T Ω)`.

The actual dilation suggests that the Hilbert-space sandwich
`Γ(first)† Γ(rotation) Γ(first)` equals degree damping on every full Fock vector.
Once this identity and genuine vacuum separation on the prescribed double
commutant are proved, degree damping composition would imply the intrinsic
semigroup law without a polynomial-density assumption for the double commutant.
This remains proposed mathematics here, not an assumed interface.

Order-supremum normality, L¹ extensions, hypercontractivity, logarithmic Sobolev
inequalities and entropy results remain separate obligations. The vacuum state
is not claimed faithful or tracial for an arbitrary non-orthonormal complex
field family by this construction.
