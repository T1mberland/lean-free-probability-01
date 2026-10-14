# Full actual finite mixed matrix OU suffix decomposition

## Verified achievement

For any orthonormal family e:I→H in a complete complex Hilbert space, every
finite matrix index ν (including empty), any finite word set S, arbitrary
coefficients C_w:Matrix ν ν ℂ, and t≥0, put α=exp(−t),

    F = Σ_{w∈S} C_w ⊗ W_w,
    F_{s,α} = Σ_{w∈S, s suffix w} α^(|w|−|s|) C_w ⊗ W_(take(|w|−|s|)w).

The kernel verifies the full actual amplified identity

    P_t(F F*) = F_{[],α} F_{[],α}*
      + (1−α²) Σ_{s∈tails(S), s≠[]} F_{s,α} F_{s,α}*.

There is no homogeneity, finite-alphabet, spanning, countability, nonempty matrix
index, or nonempty word assumption. `tails(S)` is the actual finite union of
the tails of the finitely many supported words. Matrix products retain the
noncommuting coefficient order C_u C_v*. The actual output is nonnegative in
the full canonical C-star matrix operator cone, via the genuine finite Hilbert
block star-algebra equivalence and reflection of positivity.

`actualFamilyWordOUMatrix_mixed_amplitude_Gram` is the general finite-set result.
`actualFamilyWordOUMatrix_finsupp_suffixGram` identifies it literally with the
previously defined `matrixSuffixGram` for finite-support coefficients. It thus
discharges the equality obligation previously left open in the historical
homogeneous/candidate notes, without editing those frozen files.

The amplified map is the already verified actual transported prescribed-family
map: native equivalence inverse, actual inclusion in the literal family double
commutant, genuine `ouVonNeumannTimeCP`, and faithful cyclic word representation.
No abstract multiplier or desired suffix decomposition is used as an assumption.

## Real parameter and endpoint scope

Adjoint amplitude weights conjugate the scalar parameter. The actual matrix
amplitude result uses real α=exp(−t), not arbitrary complex α. The helper
`real_scaled_mul_star_power` proves the exact real adjoint weight rule. The
pairwise algebraic identities are division-free and allow real parameter zero,
with 0^0=1. The actual OU theorem is at finite nonnegative time; it does not
assert an infinite-time map from that endpoint observation.

## Frozen source milestones

Twelve new modules under FreeProbability/Fock form this checkpoint. All twenty-
two earlier suffix/actual-OU/marginal/order modules remain unchanged.

- b5ede0f, WickMixedSuffixGramContractions: actual general common-suffix length
  contractions, symmetric minimum-degree range, and unequal-prefix cut tests.
- 86a79df, WickMixedSuffixGramPartial: common shorter suffixes and exact nested
  unequal-prefix Gram partial contraction sums.
- 9563450, WickMixedSuffixGramWeights: division-free shifted residual-degree
  summation by parts.
- f677f76, WickMixedSuffixGramPairwise: real-parameter pairwise mixed suffix
  identity, with the actual residual-degree shift.
- 98b9985, WickMixedSuffixGramLengths: literal nonempty suffix-length reindexing.
- 76ba8a8, WickMixedSuffixGramSuffixSums: actual finite bijection of nonempty
  common terminal words with contraction lengths.
- af90a19, WickMixedSuffixGramActualOU: closed-word mixed contractions and
  genuine transported OU product identities, without an equal-degree premise.
- 400ee20, WickMixedSuffixGramWeightedSums: true real adjoint powers and exact
  actual OU pairwise terminal-word sum.
- cd1dfd5, WickMixedSuffixGramMatrix: ordered actual amplified mixed product.
- 529d34f, WickMixedSuffixGramPrefixTerms: real weighted matrix prefix terms,
  their actual star-product weights and finite common support extension.
- d441297, WickMixedSuffixGramFinite: full actual arbitrary mixed finite matrix
  suffix Gram identity and canonical cone positivity.
- f7de8f7, WickMixedSuffixGramFinsupp: exact identification of the original
  finite-support residual amplitudes, suffix support, and actual Gram candidate.

## Verification and publication

All final focused builds explicitly returned exit zero under the common build
lock. Twenty-eight principal direct theorem axiom audits explicitly returned
exit zero with only subsets of propext, Classical.choice, Quot.sound. Every
source commit followed its terminal audit and was immediately pushed successfully
to feat/fock-mixed-suffix-gram. Source integrity and whitespace checks passed.
Coordinator mathematical review and checked-main integration remain separate.

The resolved Lean errors were ordinary lemma names, explicit real power/product
arguments, explicit matrix star-zero types, and congruent natural-subtraction
normalization. An equality simplifier changed which terminal-word length was
visible; rewriting the corresponding second-word length resolved it. No new
axioms, kernel bypass, weakened desired statement, or resource-limit increase
was introduced.

## Remaining mathematical obligations

This completes the finite mixed positive suffix identity, not Goal 10 or an
entropy theorem. The homogeneous common marginal and complete matrix order
bound remain valid. For mixed degrees, the weighted suffix marginals vary;
the unweighted cut marginal theorem does not imply equality of these weighted
marginals or remove interference among prefix lengths. A flagged/conditional
entropy argument and its actual matrix marginal bookkeeping must be developed.
Support-aware relative entropy, singular marginal functional calculus,
operator logarithm monotonicity, convexity/data processing, L1 extensions and
approximation remain independent obligations.
