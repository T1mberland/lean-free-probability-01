# Independent colored Haar centered traces: reviewed, unproved plan

The actual single-Haar criterion with independent random input data is verified
on its development branch. The following multicolor extension is a reviewed
mathematical plan; cyclic grouping and the induction are not yet kernel proved.

Use strong induction on the positive length m of an alternating centered word
of blocks `U_c A U_c*`. The input matrices are measurable functions of shared
data, uniformly bounded in the genuine Euclidean operator norm and centered
for the normalized trace. Data may have arbitrary internal dependence.

The crucial independence premise is joint: the entire tuple of input data and
other Haar colors must be independent of the selected U_c. Pairwise independence
of data from each Haar plus mutual independence of the Haar family is insufficient.
Use joint independence of the augmented dependent family `Unit ⊕ colors`, or
prove the equivalent product law from data independent of the entire Haar tuple.
There is no independence assumption across matrix dimensions.

For a cyclically alternating word of length m≥2, choose an occurring color c
and split at its occurrences. Every intervening other-color run B_j is nonempty,
shorter than m and linearly alternating. Induction gives `τ_N(B_j)→0` almost
surely. A single occurrence of c is valid: its run has length m−1.

Replace B_j by `B_j−τ_N(B_j)I`. These are genuinely centered with a uniform
bound such as `2(K+1)^m`. The selected-color A_j and centered runs are all
functions of the tuple independent of U_c. The actual single-Haar random-input
criterion makes the centered grouped trace tend to zero. A finite ordered
multilinear telescoping identity, actual operator bounds and `τ_N(B_j)→0`
restore the original trace. The matrix products must be reconstructed in their
true cyclic order; no noncommutative reordering is allowed.

For a linearly alternating word whose first and last colors match, m≥3.
Rotate the trace, multiply the endpoints in order `A_last*A_first`, and center
that merged coefficient in its original family. The centered part has a
cyclically alternating word of length m−1. The scalar part is the bounded
`τ_N(A_last*A_first)` times the centered interior word of length m−2, which
is positive and shorter. Induction handles both. A length-one word has exactly
zero centered trace; an empty word has value one and must never be treated as
a vanishing centered word. Dimension zero follows the existing convention and
does not affect dimension tending to infinity.

Earliest kernel tasks are actual trace centering and the norm bound; finite
ordered product perturbation; genuine cyclic run segmentation/reassembly and
shorter/nonempty proofs; augmented tuple independence extraction; then strong
word-length induction. Pinned APIs include `iIndepFun.indepFun_finset` followed
by `IndepFun.comp` and finite intersections of almost-sure events.

This route suggests a genuine multicolor centered freeness criterion without
classifying leading pairing geodesics. Expected traces and probability limits
can follow bounded convergence. Marginal joint star-moment limits and target
distribution interfaces remain separate. Uniform bounds and moment convergence
alone do not imply strong operator convergence or spectral inclusion.
