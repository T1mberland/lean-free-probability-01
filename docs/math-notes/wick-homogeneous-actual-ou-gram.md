# Actual amplified homogeneous OU suffix decomposition

## Verified mathematical statement

For any orthonormal family e:I→H in a complete complex Hilbert space, any
finite matrix index ν (including empty), any finite set S of words of common
degree n, any coefficients C_w:Matrix ν ν ℂ, and t≥0, the actual transported
amplification of the genuine prescribed-family OU map satisfies

    P_t(F F*) = α^(2n) G_n + (1−α²) Σ_{h<n} α^(2h) G_h,
    α = exp(−t),  F = Σ_{w∈S} C_w ⊗ W_w.

G_h are the previously verified actual finite suffix-cut star-square Grams.
The equality is in CStarMatrix ν ν B(WordSpace I), and the output is proved
nonnegative in its full canonical cone. Matrix multiplication retains C_u C_v*.
No finite-alphabet, spanning, or countability assumption is imposed.

The map called `actualFamilyWordOU` is defined, not assumed, as

    σ ∘ ouVonNeumannTimeCP e t ht ∘ ouCyclicNativeInclusion e
      ∘ (familyNativeWordEquiv e he).symm.

Its genuine entrywise matrix amplification is `actualFamilyWordOUMatrix`.
`actualFamilyWordOUMatrix_entry` states its exact connection to the actual native
whole-double-commutant CP map. Input closed-word amplitudes correspond through
the actual native star-algebra equivalence to original family operators. The
codomain of this transported linear map is the full word operator algebra;
no closed-word range assertion for general inputs is built into the definition.

## Source commits and principal interfaces

All four bridge sources are new, under FreeProbability/Fock. The eleven earlier
suffix sources and their notes at `a273f45` remain unchanged.

- `530deec`, WickSuffixGramActualOU:
  `familyNativeWordEquiv_symm_closedWick` identifies actual native Wick preimages;
  `familyWordRepresentation_OU_Wick` proves the true represented whole-family
  eigenvalue using actual vacuum coefficients and commuting right fields;
  `actualFamilyWordOU` and its closed-Wick eigenvalue are genuine transported maps.
- `7c54dae`, WickSuffixGramActualOUProduct:
  actual contractions within the closed word algebra and exact actual OU of
  homogeneous products, using linearity and true Wick eigenvalues.
- `fc2c698`, WickSuffixGramActualOUMatrix:
  actual matrix amplification, exact ordered products inside the closed algebra,
  and the amplified actual homogeneous product contraction identity.
- `8333e75`, WickSuffixGramActualOUFinite:
  finite closed matrix amplitudes; `actualFamilyWordOUMatrix_entry`;
  `actualFamilyWordOUMatrix_amplitude_product` identifies the true OU output
  with the earlier literal contraction polynomial;
  `actualFamilyWordOUMatrix_amplitude_Gram` gives the actual Gram decomposition;
  `actualFamilyWordOUMatrix_amplitude_nonneg` proves canonical matrix positivity.

The source chain proves the actual map equality; it does not use a hypothetical
linear multiplier as a premise. The earlier homogeneous literal polynomial
identity is reused only after its equality with the actual map is proved.

## Checks and publication

All final focused builds explicitly returned exit zero under the common build
lock. Eleven principal direct axiom audits explicitly returned exit zero with
only propext, Classical.choice, Quot.sound. Every source commit was made only
after its terminal audit and then immediately pushed successfully to
feat/fock-homogeneous-gram-ou. Source integrity and whitespace checks passed.
Coordinator integration and mathematical review remain separate checkpoints.

The main Lean repairs were explicit coercions for star-algebra equivalence
injectivity, conversion via its toStarAlgHom.toLinearMap, an explicitly typed
zero-scalar lemma, and explicit finite star-sum arguments. These repaired
ordinary elaboration errors without resource-limit changes or new assumptions.

## Remaining obligations

The proved result is homogeneous and finite. The arbitrary mixed-degree suffix
identity remains open. Common matrix marginal identities and quantitative
canonical matrix order bounds are distinct next dependencies. Relative entropy,
singular marginals, data processing, conditional entropy and noncommutative L1
are unproved here. This checkpoint does not complete Goal 10 and does not assert
surjectivity of the whole double-commutant representation onto a word von
Neumann algebra.
