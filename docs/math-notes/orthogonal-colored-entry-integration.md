# Actual finite-color orthogonal Haar entry integration

Published checkpoints on `feat/orthogonal-colored-entry-integration`, based on
frozen random-input checkpoint `321f28e`:

- `82e7d7f`: `OrthogonalColoredEntryIntegration.lean`.
- `52fbb46`: `OrthogonalColoredEntryWeingarten.lean`.
- `0784395`: `OrthogonalColoredEntrySites.lean`.

All prior sources remain unchanged and frozen.

## Genuine random hypotheses and joint law

For a finite color type I and actual orthogonal random matrices X_c on a
common measurable source space, the hypotheses are actual `iIndepFun X μ`
and actual measure-preserving normalized compact Haar marginals.
`independent_coloredHaar_measurePreserving` proves the full actual joint law
is the genuine finite product of Haar measures. No joint-law formula or
entry-integration identity is assumed. Empty color indices are retained;
the actual independence interface implies normalization of the source.

`coloredEntryMonomial` is the literal product of actual real matrix entries
with a possibly different degree k_c for each color. Its actual Bochner
integral is `coloredEntryIntegral`. Genuine integrability follows from
continuity on the compact finite product group and the proved joint-law map.

## Actual factorization and parity

`coloredEntryIntegral_eq_product` proves

```
actual integral of ∏c entryMonomial(i_c,j_c,X_c) = ∏c actual entryMoment(i_c,j_c).
```

The proof uses the actual finite probabilistic independence integral theorem
and measure-map transport of the genuine one-color Haar integrals. Every
zero-degree color contributes the genuine scalar moment one, and an odd
degree at any color forces the actual entire integral to zero. No independence
between matrix dimensions or extra trace/positivity premise is introduced.

## Genuine color-respecting Weingarten formula

For even per-color degree 2r_c and the explicit stable condition r_c≤N at
EVERY color, the actual integral equals the product of previously proved
one-color genuine inverse-Gram pairing sums. Finite product-of-sums gives

```
Σ(p : ∀c, OrdinaryPairing(r_c)) Σ(q : ∀c, OrdinaryPairing(r_c))
  ∏c delta(p_c,i_c) G_(N,r_c)^(-1)(p_c,q_c) delta(q_c,j_c).
```

The weights are ACTUAL inverses of actual ordinary-pairing Gram matrices.
All ordinary pairings are retained, including crossings. Zero-degree colors
and an empty color family are covered by the same formula. No low-dimensional
pseudoinverse formula is claimed outside the explicit stable hypotheses.

## Original site order and nonadjacent colors

`ColoredEntrySites color c` is the actual fiber of an arbitrary map from a
finite original site type S to the color type I. The source constructs an
actual bijection from Fin of its TRUE cardinality to that fiber. The actual
site product regrouping is proved via the genuine sigma-of-fibers equivalence;
no supplied reordering or degree-count identity is used.

Thus the original-site integral is genuinely integrable and equals the product
of true fiber moments. Odd actual fiber cardinality kills it. If every actual
fiber cardinality equals 2r_c and every r_c≤N, then
`coloredSiteIntegral_eq_weingarten_sum` proves the same genuine color-respecting
pairing double sum directly for the product in its ORIGINAL site order.
Color labels may repeat nonadjacently; no adjacent or pairwise-distinct shortcut
is imposed. Empty site sets and empty fibers are included.

## Verification and remaining dependencies

Focused builds passed warning-free with explicit exit zero: 3059, 3060 and
3061 jobs. All 7, 2 and 10 public declarations respectively were directly
transitively audited with only `propext`, `Classical.choice`, `Quot.sound`, or
fewer. Source integrity and whitespace/diff checks passed at each atomic
checkpoint, and every source commit was immediately pushed successfully.
The first build waited for the shared lock; no concurrent heavy build was
started. A harmless unused zero-degree color binder was removed before
publication. No proof statement was weakened to resolve elaboration.

These are actual colored-entry integration formulas. Colored trace-word
expansion, genuine colored contraction geometry, centered cancellation and
full joint star-moment/asymptotic-freeness packaging remain separate next
obligations. The previous single-Haar independent-random-input almost sure
criterion remains available, but is not silently identified with a full
multicolor joint-limit theorem. Strong convergence and spectral inclusion
are also not proved by this entry formula. Integration and goal certification
remain coordinator responsibilities.
