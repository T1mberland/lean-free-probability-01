# Quantitative finite-depth exterior resolvents: execution plan

This is a reviewed mathematical plan, not a completed Goal5 theorem.
Root `c9acaaa` proves `geometricInverse_apply_comparison`: actual geometric
inverses differ on x by at most `2q^(L+1)/(1−q)‖x‖` when the first L+1
operator powers agree on x, with both norms bounded by 0≤q<1. This includes
the zero Banach space and q=0. Actual Fock retained powers are still to prove.

`FiniteDepthProjection` constructs the literal finite set of all words of
length at most L and its orthogonal coordinate projection. Its range equals
the finite word span, is finite dimensional, contains the vacuum, and the
projections converge in norm on every completed Fock vector. The alphabet
must be finite here; an empty alphabet remains valid.

Next use the actual matrix-Hilbert operator representation of the general
Hermitian pencil H=`operatorMatrixPencil C₀ C`, with top edge b. Put c=‖H‖
and A=H+cI. Actual spectral order gives `0≤A≤(b+c)I`, so b+c≥0.
For every real z>b, d=z+c>0 and q=(b+c)/d lies in [0,1).

An important domain correction: ambient QHQ has an extra zero eigenvalue
outside the retained range. When b<0, z>b does not make zI−QHQ invertible.
Use the true restricted depth-subspace operator, or compress the SHIFTED
positive operator `A_L=Q(H+cI)Q` and invert dI−A_L on the ambient space.
Its outside-range inverse is d⁻¹I and does not affect vacuum compression.
On the retained range this is exactly the intended truncated pencil inverse.

The actual field word actions must prove H maps depth≤k into depth≤k+1.
Consequently `Q A^k Jv=A^k Jv` for k≤L, and induction gives
`(QAQ)^k Jv=A^k Jv`, where J is the actual matrix vacuum inclusion.
Both shifted operators have norm at most b+c. Apply the generic tail lemma
to A/d and A_L/d and compress with J* and J to obtain the proposed bound

`‖m(z)−m_L(z)‖ ≤ 2 q^(L+1)/(z−b)`.

This uses general Hermitian coefficients, with neither positivity nor
commutativity imposed. If b+c=0, positivity forces A=0, and the resolvents
agree exactly. Singular limits z↓b and deterministic edge subspace
certificates remain later mathematical obligations, even after this bound.

The queue is: retained-power generic estimate; actual finite-depth projection;
actual pencil propagation; shifted-positive spectral bounds/compression;
genuine matrix vacuum resolvent estimate; boundary certificates/singular limits.
