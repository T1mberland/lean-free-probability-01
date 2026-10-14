# Actual Haar entry-moment pairing approximation

Source milestone: `9843e9c`,
`FreeProbability/RandomMatrix/OrthogonalEntryMomentAsymptotics.lean`.
Dependency: actual Weingarten formula `e4b842f` and uniform inverse error
`406b97a`. All earlier sources remain unchanged.

## Verified statement

For each fixed `r`, eventually in `N`, simultaneously for all tuples
`i,j : Fin (2*r) → Fin N`,

```
|N^r entryMoment(i,j) - Σp δp(i) δp(j)| ≤ 2 card(OrdinaryPairing r)^3 / N.
```

Here `entryMoment` is the actual normalized orthogonal Haar integral, not
an abstract function constrained by a pairing formula. The sum uses ALL
intrinsic ordinary pairings, crossing included. This is a moving-dimension,
uniform-over-tuples estimate; a fixed-domain limit of tuples is not asserted.
Half-degree zero is included. The dimension threshold is existential and
independent of the tuples.

Public declarations in `FreeProbability.Orthogonal`:

- `ordinaryPairingDelta_abs_le_one`.
- `rescaled_entryMoment_sub_pairing_sum`: exact finite double-sum error
  expansion in stable dimension `N≥r`.
- `eventually_rescaled_entryMoment_error_le`: the displayed uniform bound.

The exact diagonal contribution of the genuine inverse formula is the
matching-pairing sum. Each paired delta has absolute value at most one.
Bounding both finite pairing sums yields the explicit constant. No
optimality of that constant is claimed.

Focused compilation passed without warnings (3025 jobs); all three
public declarations' transitive audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. Source integrity and whitespace checks
passed, and the source commit was pushed immediately. A linter fix removed
an unused finite-type assumption from the delta lemma; the attempted first
placement of `omit` after a documentation comment was syntactically invalid
and was corrected before any publication.

## Earliest remaining trace-word dependencies

The repository search found no existing normalized trace-word integration
or pairing-distance theorem. Entrywise leading matching approximations alone
do not justify normalized trace-word limits: summing over dimension-dependent
matrix indices can amplify the uniform `1/N` error.

A proposed next independent combinatorial milestone is the actual distance

```
d(p,q) = r - card(Quotient(pairingSetoid p.out ⊔ pairingSetoid q.out)).
```

Its nonnegativity and zero-separation follow from the already proved loop
bounds. The missing triangle inequality is
`d(p,s) ≤ d(p,q)+d(q,s)`. A finite partition-rank/submodularity argument or an
explicit minimal pairing-switch path can prove it; neither is assumed in
current results. This supplies the exponent control for a genuine Neumann
path expansion of the normalized Gram inverse, with target
`N^r |G_N^{-1}(p,q)| = O(N^{-d(p,q)})` off the diagonal. The existing actual
leading limits and reciprocal estimate are weaker than this target when
`d(p,q)>1`.

The first actual trace-word interface should expand, for deterministic real
matrices `A₁,…,Aᵣ,B₁,…,Bᵣ`,

```
N^{-1} ∫ Tr(A₁ U B₁ Uᵀ ⋯ Aᵣ U Bᵣ Uᵀ) dHaar(U)
```

into the true finite pairing sum with deterministic matrix-index
contractions. It must prove the expansion from matrix multiplication,
transpose, trace and finite-integral linearity, then give contraction bounds
under genuine uniform operator-norm hypotheses. Its pairing-cycle count
must be related to the inverse-distance exponent. Finally, for alternating
centered deterministic blocks, the candidate leading contractions must
vanish using their actual normalized traces. These are missing mathematical
steps, not assumptions added to the present moment theorem.

Multiple independent Haar matrices need actual product Haar integration and
color-respecting contractions. Expected trace limits, fluctuations,
concentration, and almost-sure convergence require separate theorems. The
current result makes no joint asymptotic-freeness claim. Low-dimensional
invariant spanning/pseudoinverse obligations also remain separate.
