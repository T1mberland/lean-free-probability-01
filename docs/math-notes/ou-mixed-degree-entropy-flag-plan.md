# Mixed-degree entropy via a length flag: reviewed, unproved plan

This strengthens the earlier positive suffix-Gram design record. The reviewer
checked the mathematical route in finite tracial quantum probability. None of
the new entropy, flag or mixed-degree identities below is kernel proved.
Goal10 remains open; all obligations below must be implemented honestly.

The proposed full mixed-degree positive suffix formula is
`P_α(FF*)=Σ_s w_s F_s F_s*`, where `w_[]=1`, `w_s=1−α²` otherwise and
`F_s=Σ_l F_{s,l}` has coefficient damping α^l on residual prefix length l.
Its component marginal is `ρ_s=Σ_l ρ_{s,l}`, with
`ρ_{s,l}=E(F_{s,l}F_{s,l}*)`; different suffix marginals are allowed.
Weighted suffix marginals sum to the original `ρ=E(FF*)` by telescoping.
The actual homogeneous formula is proved; the full mixed formula is still open.

Choose α²<β<1 and `p_l=(1−β)β^l`. For a fixed suffix form the finite flag
Gram `Y_lm=F_{s,l}F_{s,m}*/sqrt(p_l p_m)` and reference
`Σ=diag(ρ_{s,l}/p_l ⊗1)`. This is a genuine positive block Gram. Input and
reference have the same mass `m=Σ_l q_l/p_l`, with `q_l=Tr ρ_{s,l}`.
The contraction row `K=(sqrt p_l)_l` sends Y to F_sF_s* and Σ to ρ_s⊗1.
Their output masses equal `q=Σ_l q_l`, because actual different-degree Wick
orthogonality kills cross terms. Active flag indices are finite, so ‖K‖≤1.

Use trace-decreasing CP data processing with a scalar failure flag carrying
the lost trace. Both lost traces equal m−q, so the failure relative entropy
is zero. This requires a proved CP extension and a genuine entropy theorem;
ordinary unital-map DPI cannot simply be asserted for this compression.

The proposed exact chain rule is
`D(Y||Σ)=Σ_l D(Y_ll||Σ_ll)+D(Y||diag Y)`.
The genuine homogeneous canonical order bound would give
`D(Y_ll||Σ_ll)≤(q_l/p_l)[l log r+2 log(l+1)]` for finite alphabet rank r≥1.
The coherence term has the standard bound
`D(Y||diag Y)≤m H((q_l/p_l)/m)`.
Gibbs comparison with the geometric distribution gives
`m H≤−logβ Σ_l l q_l/p_l −log(1−β)m`.
These pinching, support-aware logarithm and entropy statements are missing
mathematical dependencies, including singular and zero-mass blocks.

Joint convexity in BOTH arguments then combines suffix components with their
varying marginals. Put a=α²/β<1. For each original coefficient word of length n,
the aggregate input mass per coefficient trace is

`(1−β)^−1 [a^n+(1−α²)Σ_(l<n) a^l]`.

The corresponding aggregate degree mass is
`(1−β)^−1 [n a^n+(1−α²)Σ_(l<n) l a^l]`.
Both have uniform bounds independent of n. Thus the route suggests a finite
constant depending only on r and α, independent of matrix size and degree,
for EVERY finite mixed-degree amplitude. The geometric ratio removes the
unwanted degree growth; scalar L2 regularization alone does not prove this.

To reach bounded positive whole-von-Neumann matrix X, use P_(t/2)X in the
native Cstar matrix algebra, take its genuine native square root, and approximate
that root in norm by finite Wick matrix amplitudes. Actual matrix CP contraction
and the semigroup identify the outputs with approximations to P_tX. The entropy
limit requires JOINT lower semicontinuity, since the matrix marginal ρ_n varies.
This uses a constant at t/2 and avoids assuming norm polynomial density in the
whole von Neumann algebra. Entrywise native membership must be lifted honestly
to the native canonical matrix cone before taking the square root.

The full noncommutative L1 extension and positive approximation remain separate
obligations after bounded X. Other missing steps are the actual mixed suffix
identity, canonical matrix order bound, trace-decreasing DPI with failure,
pinching/coherence and Gibbs bounds, joint convexity and joint lower semicontinuity.
An empty alphabet has only degree zero; a formula containing log r needs r≥1.
