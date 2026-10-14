# Exact native closed-word image

## Verified scope

For an arbitrary orthonormal family `e : I → H` in a complete complex Hilbert
space, with no spanning or countability assumptions, the original norm-closed
field algebra `tensorFamilyAlgebra e` is isometrically star-algebra equivalent
to `closedSemicircularAlgebra I`. This uses the actual cyclic representation
constructed from the original family cyclic Hilbert space.

The whole double-commutant representation is not asserted to be onto the word
von Neumann algebra. The stronger, useful membership criterion is instead:

`familyWordRepresentation e he T ∈ closedSemicircularAlgebra I` if and only if
`(T : TensorFullFock H →L[ℂ] TensorFullFock H) ∈ tensorFamilyAlgebra e`.

This lets a norm-convergent closed-word Wick reconstruction, once identified
with the actual represented damped operator, establish native C-star membership.
It does not assume operator-norm density of polynomials in the double commutant.

## Construction and declarations

- `FamilyCyclicBasisNativeImage.lean`, commit `359200d`:
  `familyNativeWordRepresentation` restricts the verified faithful cyclic
  representation along the actual native inclusion. Its exact field and Wick
  images, injectivity, isometry, closed range, and range equality are proved.
  Forward membership uses the genuine native polynomial density and actual
  finite Wick span. Reverse membership uses completeness of the isometric
  image, exact generator images, and minimality of the norm-closed adjoin.
- `FamilyCyclicBasisNativeEquiv.lean`, commit `0554f84`:
  `familyNativeWordHom_bijective`, `familyNativeWordEquiv`, its norm equality,
  and `familyNativeWordEquiv_preimage` give unique actual native preimages of
  every closed word operator. `familyWordRepresentation_mem_closed_iff`
  additionally uses whole-double-commutant representation injectivity to detect
  the original native subalgebra.

The six earlier family cyclic basis/representation modules through `cc4dbd3`
remain unchanged. No identification of the family cyclic space with the entire
ambient tensor Fock space is used.

## Verification and publication

Both focused final module builds completed with exit status zero under the
common `/tmp/lean-fp-build.lock`. Twelve principal theorem axiom audits completed
with exit status zero and reported only `propext`, `Classical.choice`, and
`Quot.sound`. The proof-source integrity guard and whitespace checks passed.
Both source commits were immediately pushed successfully on
`feat/fock-family-native-image`. Coordinator integration is a separate check.

A first proof attempt needed explicit subtype coercion types and the predicate
for dense-range induction. A generic inferred `StarAlgEquiv.norm_map` call hit
Lean's ordinary typeclass heartbeat limit; explicitly using the ambient native
representation and its injectivity resolved it without increasing any limit.
No resource exhaustion, new axioms, or kernel bypass occurred.

## Remaining obligations

Positive-time reconstruction must still be matched with the actual OU map by
its true vacuum coefficients and commuting right fields. This image theorem
supplies the final native-range step after that equality. Whole von Neumann
image surjectivity, unrelated analytic goals, and entropy results are not
consequences of this checkpoint.
