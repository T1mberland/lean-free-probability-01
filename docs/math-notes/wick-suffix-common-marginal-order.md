# Actual common suffix marginals and complete matrix order bound

## Verified statements

`matrixCutGram_vacuum_marginal` proves the actual entrywise vacuum marginal

    (id_matrix ⊗ τ)(G_h) = ρ,    ρ = Σ_{w∈S} C_w C_w*.

This holds for every cut h, every finite word set S, arbitrary alphabets, and
arbitrary finite matrix indices, including the empty type. Homogeneity is not
required: equality of the suffixes and Wick orthogonality of the prefixes
force equality of the original words via take_append_drop. Singular ρ is allowed.

For finite alphabets, `matrixCutGram_le_homogeneous` proves the actual full
canonical C-star matrix operator order inequality

    G_h ≤ (card I)^h (h+1)^2 scalarEmbed(ρ),    h≤n,

for finite homogeneous degree-n support. `matrixCutGram_le` is stronger: it only
requires h≤length(w) for every supported word. No spanning, countability,
nonempty alphabet, nonzero matrix size, or invertible marginal hypothesis is
introduced. An empty alphabet at h=0 uses 0^0=1. At positive degree the same
exact cardinal formula handles the absence of words.

The order is in CStarMatrix ν ν B(WordSpace I). Positivity and inequalities are
proved on the entire finite Hilbert block space and reflected through its
actual star-algebra equivalence. Entrywise order or product vectors do not
substitute for the full matrix cone.

## Actual mathematical construction

1. Polynomial trace and Wick orthogonality give the exact ordered entrywise
   matrix marginal of coefficient terms.
2. Genuine finite Hilbert-vector Cauchy--Schwarz gives
   (Σ A)(Σ A)* ≤ card(S) Σ AA*. The actual block star-algebra equivalence
   transports this to full canonical matrix order.
3. The actual single-word estimate ‖W_w‖≤length(w)+1 gives a full operator
   square bound, proved directly through the adjoint norm on all Hilbert vectors.
4. The actual diagonal star representation and cone conjugation prove
   (C⊗W_w)(C⊗W_w)* ≤ (length(w)+1)^2 scalarEmbed(CC*), retaining matrix order.
5. Each fixed suffix fiber injects into length-h prefix functions Fin h→I;
   its cardinal is at most (card I)^h, including all empty cases.
6. Positive scalar monotonicity, coefficient linear embedding, exact fiber
   partitioning and finite sums assemble the full cut Gram inequality.

## Frozen verified sources and commits

All seven sources are new under FreeProbability/Fock. Earlier fifteen suffix
and actual-OU source modules and their notes remain unchanged.

- c45b260, WickSuffixGramMarginal: genuine entrywise vacuum map, reversed
  star-square Wick orthogonality, ordered coefficient marginal and common ρ.
- 9e73d12, WickSuffixGramOrderCauchySchwarz: finite vector, bounded operator,
  and complete canonical finite-matrix Gram Cauchy--Schwarz.
- 2033409, WickSuffixGramOrderCoefficient: actual scalar embedding, diagonal
  star homomorphism, coefficient factorization, all-vector norm-square bound,
  single-word square bound and coefficient matrix cone sandwich.
- e217b8c, WickSuffixGramOrderCardinality: exact prefix injection and suffix
  fiber cardinal bound without nonempty alphabet assumptions.
- 74b41f1, WickSuffixGramOrderScalar: full matrix positive scalar monotonicity
  and actual linear scalar embedding of singular marginal sums.
- 8f0a0fb, WickSuffixGramOrderFiber: genuine suffix amplitude square bound.
- 611b9ab, WickSuffixGramOrder: exact marginal fiber partition, full matrix
  Gram order estimate, and its homogeneous degree wrapper.

## Checks and publication

Every final focused module build explicitly returned exit zero under the
common build lock. Twenty principal direct axiom checks, including the diagonal
star homomorphism, returned exit zero with only propext, Classical.choice,
Quot.sound. Audits finished before source commits, and every commit was
immediately pushed successfully to feat/fock-homogeneous-gram-marginal.
The source integrity guard and whitespace checks passed. Review and checked
main integration are the coordinator's separate responsibility.

The direct CFC norm-square API and a broad final scalar/adjoint normalization
hit ordinary Lean WHNF heartbeat limits. The proof was repaired with the actual
all-vector adjoint norm estimate, typed intermediate matrices, and an explicit
star-product equality. No limit was increased and no concurrent heavy builds
were started. A finite-image decision procedure mismatch was repaired using
an explicit local classical instance matching the existing Gram definition.

## Remaining obligations

The preceding actual finite homogeneous OU suffix decomposition now has the
common marginal and complete matrix order bound it requires. These are
prerequisites, not an entropy theorem. Support-aware relative entropy,
singular-marginal functional calculus, operator logarithm monotonicity,
convexity/data processing, noncommutative L1 and approximation are separate
obligations. Mixed-degree positive suffix decomposition also remains open;
the common unweighted cut marginal does not make the weighted mixed-degree
suffix marginals equal or remove interference between different prefix lengths.
