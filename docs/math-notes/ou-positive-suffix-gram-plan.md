# Positive suffix Gram decomposition: reviewed, unproved plan

This is a mathematical design record. None of the new identities or entropy
bounds below is yet kernel proved. The read-only reviewer checked their Wick
orientation against `wick_product_contractions`. Goal 10 remains open.

For a finite matrix-valued Wick amplitude `F = Σ_w C_w ⊗ W_w` and
`0 ≤ α ≤ 1`, put `F_{s,α} = Σ_u α^|u| C_{u++s} ⊗ W_u`. The proposed
exact positive decomposition is

`P_α(FF*) = F_{[],α}F_{[],α}* + (1−α²) Σ_{s≠[]} F_{s,α}F_{s,α}*`.

Only finitely many suffixes contribute. Products preserve the actual matrix
coefficient order `C_w C_v*`. In `W_w W_v*`, the Wick contractions match a
common suffix of `w,v`, because the second Wick word is reversed by the star.
For contraction length j, the coefficient telescopes:

`α^(|w|+|v|) + (1−α²) Σ_{h=1..j} α^(|w|+|v|−2h)
 = α^(|w|+|v|−2j)`.

The endpoint α=0 must preserve the convention `0^0=1`. The next independent
kernel milestone is the finite actual matrix identity and positivity in the
canonical matrix operator cone, with no assumed contraction formula.

For homogeneous degree n, define `F_s = Σ_{|u|=n−k} C_{u++s} ⊗ W_u`
for `|s|=k`, and `G_k = Σ_{|s|=k} F_sF_s*`. Then

`P_α(FF*) = α^(2n)G_0 + (1−α²) Σ_{k=1..n} α^(2(n−k))G_k`.

Every `G_k` has the same matrix marginal `ρ=Σ_w C_wC_w*`. Residual degree
l=n−k has mass `(1−α²)α^(2l)` for l<n and tail mass `α^(2n)` at n.
For α<1 its mean is at most `α²/(1−α²)`, independently of n.
For a finite alphabet of size r≥1, finite operator Cauchy–Schwarz and the
actual single-word bound suggest the canonical matrix order inequality

`G_k ≤ r^l(l+1)^2 (ρ ⊗ 1)`.

This is a complete matrix inequality; entrywise or product-vector positivity
does not suffice. It requires a genuine ordered finite-operator proof.

Conditional on a developed support-aware relative entropy calculus, operator
log monotonicity and convexity with the common marginal would give a uniform
homogeneous bound, for example `(log r+2)α²/(1−α²)` times `Tr ρ`.
This is not a proven entropy theorem. Singular marginals, conditional entropy,
data processing, approximation and noncommutative L1 remain obligations.

For mixed degrees the positive suffix identity still works, but the component
marginals `ρ_{s,α}=Σ_u α^(2|u|)C_{u++s}C_{u++s}*` vary. Their weighted sum
is ρ. The homogeneous common-marginal argument cannot be applied directly:
a separate conditional or flagged decomposition must control interference
between prefix lengths. Plain scalar L2-to-operator regularization does not
establish a complete matrix entropy bound. For an empty alphabet only degree
zero contributes; a formula containing log r requires r≥1 explicitly.
