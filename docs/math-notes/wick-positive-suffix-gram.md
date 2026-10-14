# Verified finite homogeneous suffix Gram prerequisites

## Exact achievement and scope

For a finite set S of words of a common degree n, arbitrary complex matrix
coefficients C_w, an arbitrary alphabet I, and an arbitrary finite matrix index
ν (including the empty type), the literal degree-damped Wick contraction
polynomial has the exact actual C-star matrix identity

    D_α = α^(2n) G_n + (1−α²) Σ_{h<n} α^(2h) G_h.

Here G_h is the sum, over actual suffixes s=w.drop h of S, of B_s B_s*, where
B_s = Σ_{w∈S, w.drop h=s} C_w ⊗ W_(w.take h). Every G_h is positive in the
full canonical C-star matrix operator cone. For real 0≤α≤1 the literal D_α
is also positive. No entrywise or product-vector criterion substitutes for the
matrix cone. All coefficient products retain the order C_u C_v*.

This checkpoint does NOT yet identify D_α with the actual amplified OU image
of FF*. It does not yet prove the general mixed-degree suffix decomposition,
a common-marginal estimate, or an entropy theorem. Those remain explicit next
obligations. The separate mixed-degree candidate `matrixSuffixGram` has proved
canonical positivity and finite suffix support, but its desired OU equality is
unproved.

## Verified source history

All eleven new sources are under `FreeProbability/Fock/` and are frozen at this
checkpoint. Earlier family/native/cyclic sources remain unchanged.

- `558a9c2`, WickSuffixGramContractions: actual global `star_wick`, adjoint
  contractions, and exact common-suffix bounded-operator contraction formula.
- `d4cdea8`, WickSuffixGramWeights: division-free telescoping including α=0
  with 0^0=1, and nonnegative real suffix coefficients.
- `8357839`, WickSuffixGramAmplitude: genuine finite-support actual operator
  matrices; residual prefix amplitudes; zero outside finite tails support;
  canonical positivity of the mixed-degree Gram candidate only.
- `6ea12ee`, WickSuffixGramMatrixProduct: exact ordered C_u C_v* matrix product.
- `7758cae`, WickSuffixGramHomogeneous: homogeneous terminal-cut equality and
  nested common-suffix/prefix contraction equivalence.
- `0c5fbe2`, WickSuffixGramPartialSums: genuine prefix Gram equals partial
  contraction sums, and monotonicity of common terminal cuts.
- `0a295d5`, WickSuffixGramSummation: finite complex-module summation by parts,
  with no division or nonzero-parameter restriction.
- `87cb177`, WickSuffixGramPairwise: actual homogeneous pairwise suffix Gram
  identity for every complex parameter.
- `557f9b2`, WickSuffixGramMatrixPairwise: lifts the pairwise identity to actual
  finite C-star matrices and preserves coefficient multiplication order.
- `15b36f7`, WickSuffixGramFibers: generic exact finite Gram fiber regrouping
  in a noncommutative star ring.
- `50c7395`, WickSuffixGramFinite: exact homogeneous finite matrix decomposition,
  actual positive suffix Grams, and canonical positivity of the literal damped
  contraction polynomial.

## Verification and publication

Every final focused module build explicitly completed with exit status zero
under `/tmp/lean-fp-build.lock`. Twenty-five principal theorem direct audits
completed with exit status zero and only subsets of `propext`,
`Classical.choice`, and `Quot.sound`. The proof-source integrity guard and
whitespace checks passed. All commits were immediately pushed successfully to
`feat/fock-positive-suffix-gram`. Coordinator integration/review is separate.

There was one audit-sequencing mistake: `0c5fbe2` was committed and pushed after
its successful focused kernel build, while its separate transitive audit was
still queued under the lock. The coordinator was informed immediately and told
not to integrate it before the audit finished. That audit subsequently returned
exit zero with standard axioms, explicitly reported before further publication.
The commit history was preserved, without rewriting or pretending the ordering
was correct. Subsequent commits waited for audit completion before publication.

## Proof obstructions resolved

A real scalar-action positivity instance for the C-star matrix cone did not
infer. The definitions instead use explicit complex casts of real parameters;
positivity is transported/reflected by the genuine finite Hilbert block
star-algebra equivalence and the actual bounded-operator cone. No mathematical
assumption or resource limit was added.

Broad expansion of products of two finite sums swapped which index was outer;
using ordered sequential sum-multiplication rewrites preserved the intended
coefficient order. Terminal-cut condition rewrites needed `simp` to respect
dependent decidability. The generic fiber theorem and list-specialized theorem
use distinct decidable-equality implementations; explicit classical image
construction plus the genuine subsingleton equality of decision procedures
reconciled them. This is an ordinary kernel proof, not a bypass.

## Next independent steps

First link the literal homogeneous damped contraction polynomial to the actual
OU image using its proved Wick degree eigenvalues, then transport the matrix
Gram decomposition to native prescribed-family algebras if needed. Prove
homogeneous common matrix marginals and genuine matrix order bounds separately.
The mixed-degree decomposition requires its own residual-degree bookkeeping;
one must not infer it from the homogeneous theorem or assume common marginals.
Relative entropy, singular marginal treatment, data processing and L1 remain
independent mathematical obligations.
