# Original-family cyclic Hilbert basis and actual word operator representation

All cyclic-space statements use the ORIGINAL complete `familyCyclicSpace e`,
the norm closure of the original family-algebra vacuum orbit. The prescribed
orthonormal family is indexed by arbitrary `I` and need not span the complete
one-particle Hilbert space. No countability or nontriviality assumption is added.

## Verified source milestones

- `868baa9`, `OrnsteinUhlenbeckFamilyCyclicBasisWords.lean`:
  `familyCyclicWord e w` is the actual Wick vacuum vector with proved cyclic
  codomain. Genuine adapted full-tensor transport sends the canonical word
  `w.map d.index` to this actual vector. Injectivity of the original-family
  index map and the actual full-word Gram theorem prove its exact Kronecker
  Gram matrix and orthonormality.
- `faf7895`, `OrnsteinUhlenbeckFamilyCyclicBasis.lean`:
  the native Wick norm-span extensionality theorem and the dense native vacuum
  orbit prove that the actual cyclic-word span has zero orthogonal complement.
  Totality holds for any prescribed family; ON is needed for orthonormality.
  `familyCyclicBasis e he` is the genuine Hilbert basis indexed by `List I`.
  `familyCyclicWordUnitary e he : WordSpace I ≃ₗᵢ[ℂ] familyCyclicSpace e` is
  onto, sends each canonical original-index word to its actual Wick vacuum,
  fixes the actual cyclic vacuum, and gives the genuine unconditional word
  expansion for EVERY vector of this same complete cyclic Hilbert space.
- `f9e40cc`, `OrnsteinUhlenbeckFamilyCyclicBasisDamping.lean`:
  `familyWordDegreeDamping` is the actual bounded word-length coordinate
  multiplier on completed `WordSpace I`.
  `familyCyclicWordUnitary_damping_comp` proves its exact whole-space unitary
  intertwining with the actual complete `familyOUL2`. Every original word
  coefficient is multiplied by `exp(-t)^length`, for EVERY cyclic vector,
  not merely finite words or polynomial vacuum images.
- `f0ada6e`, `OrnsteinUhlenbeckFamilyCyclicBasisCoefficients.lean`:
  `familyVonNeumannWordCoefficients e he : tensorFamilyDoubleAlgebra e →L[ℂ]
  WordSpace I` is actual bounded whole-algebra vacuum evaluation followed by
  the inverse word unitary. It is injective, has norm `‖TΩ‖≤‖T‖`, and its
  empty-word coefficient is exactly the actual prescribed vacuum expectation.
  The actual state's inner product and quadratic norm agree with those of the
  COMPLETE square-summable coefficient vectors. Every whole-algebra vacuum
  vector has its genuine unconditional cyclic expansion, actual OU acts with
  the exact length multiplier, and actual family Wick coefficients are the
  corresponding canonical word singletons.
- `1c80524`, `OrnsteinUhlenbeckFamilyCyclicBasisOperatorsAdapted.lean`:
  the genuine isometric embedding

  `E = d.tensorTransport.symm ∘ cyclicInclusion ∘ familyCyclicWordUnitary`

  maps every completed original-family word vector into the COMPLETE adapted
  full word model. On basis words it is exactly `word(w.map d.index)`.
  Exact original word-action formulas and completed singleton-map extensionality
  prove that it intertwines BOTH canonical left and right fields on ALL vectors.
- `63afd3b`, `OrnsteinUhlenbeckFamilyCyclicBasisOperators.lean`:
  `familyWordRepresentation e he` is the actual cyclic star representation
  conjugated by the onto original word unitary. It is injective and preserves
  full operator norm. Original given left fields and original family Wick
  operators are sent exactly to canonical original-index fields and Wick
  operators. Its actual vacuum vector is the genuine whole-algebra coefficient
  vector. EVERY represented whole-double-commutant operator commutes with ALL
  original-index canonical right fields.

  The genuine full-tensor right field is constructed from the complete adapted
  full-word right field via actual tensor operator transport. It commutes with
  EVERY operator of the prescribed literal double commutant, preserves the
  ORIGINAL family cyclic space, and acts there exactly as the canonical right
  field under the original word unitary.

## Actual commutant proof and reconstruction interface

The whole-double-commutant operator, transported into the COMPLETE adapted word
model, lies in the full adapted left-field double commutant by the independently
verified interface. It therefore commutes with full adapted right fields.
The actual embedding `E` intertwines the prescribed right fields and the actual
represented operator. Injectivity of `E` proves original-word right-field
commutation. No assertion that the represented image equals a full word von
Neumann algebra is used.

The image operator's vacuum equals the true complete family coefficient vector,
and the image operator commutes with all right fields. Thus the existing genuine
right-vacuum separation theorem can identify a separately constructed norm Wick
series with the actual OU image when BOTH the series vacuum coefficients and its
right commutation are proved. This provides the proper-family reconstruction
interface without image-surjectivity or a WOT-density assumption.

## Verification and persistent decisions

All six final focused builds completed with exit code zero under the common
build lock. Forty-five principal direct axiom audits completed with exit code
zero and used only `propext`, `Classical.choice`, and `Quot.sound`.
Proof-source integrity and whitespace diff checks passed. Every mathematical
commit was pushed successfully before later development. All older frozen
cyclic representation, tensor transport, native Wick, and intrinsic OU sources
were preserved.

The totality proof uses the verified native Wick norm-span result and actual
native vacuum density. It does not assume polynomial norm density in a von
Neumann algebra. Field intertwining uses the genuine completed embedding and
exact word-action formulas, with equality extended by ℓ² singleton density.

## Exact remaining scope

The original cyclic Hilbert basis, its complete coefficients, actual OU diagonal
law, genuine word operator representation, and all-right-field commutation are
verified. Image equality/surjectivity onto a full original-word von Neumann
algebra, a normality theorem for that representation, and an explicit unitary
to a separately introduced abstract GNS completion are NOT asserted here.

A positive-time norm Wick reconstruction still requires its own genuine
operator-norm convergence, correct vacuum coefficients, right commutation,
and operator identification. Proper cyclic generator/form transfer, intrinsic
L1 extensions, hypercontractivity, logarithmic Sobolev inequalities and entropy
remain separate obligations. The original family cyclic space is never silently
identified with all ambient tensor Fock space.
