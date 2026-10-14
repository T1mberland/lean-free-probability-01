# Goal: a comprehensive, reusable free probability library in Lean 4

Develop kernel-verified algebraic, analytic, operator-valued, and asymptotic
foundations of free probability. Targets are general mathematical theorems,
independent of any particular application. Reuse and extend existing definitions,
proofs, and interfaces; inspect them before implementing new functionality.

## 1. Complete free cumulant calculus

Prove free independence if and only if all mixed free cumulants vanish. Reuse
all-order inversion and multilinearity. Develop noncrossing pairings, interval
blocks, Kreweras complements, refinement, lattice Möbius inversion, unit insertion,
adjacent-product identities, product formulas, and arbitrary-degree
moment–cumulant relations.

## 2. Full Fock semicircular systems

Construct the full Fock space
`F(H) = C Ω ⊕ ⨁_{n ≥ 1} H^{⊗ n}`, bounded left creation and annihilation operators,
and their canonical relations. For orthonormal `e_i`, define
`s_i = ℓ(e_i) + ℓ(e_i)*`. Prove self-adjointness, centering, variance one, norm two,
and free independence. Prove the vacuum state is faithful and tracial on the
**generated semicircular operator algebra**, rather than asserting these
properties on all bounded operators on Fock space.

Prove the joint free Wick formula
`τ(s_{i₁} ⋯ s_{iₙ}) = ∑_{π ∈ NC₂(n)} ∏_{ {p,q} ∈ π } δ_{i_p,i_q}`,
then Catalan moments and the semicircular spectral distribution.

## 3. Free difference quotients and integration by parts

Define free difference quotients on noncommutative polynomials by
`∂ᵢXⱼ = δᵢⱼ (1 ⊗ 1)` and the noncommutative Leibniz rule. Prove
`τ(sᵢP) = (τ ⊗ τ)(∂ᵢP)` for every polynomial and extend to matrix-valued
polynomials. Develop extensions to norm-convergent analytic functional calculus,
particularly exponentials and resolvents, with explicit domains and convergence
assumptions.

## 4. Operator-valued semicircular probability

For a unital C-star algebra `B` and completely positive covariance `η : B → B`,
develop semicircular moment recursion and the operator-valued Wick formula.
For Hermitian matrices `Aᵢ`, use `η(D) = ∑ᵢ Aᵢ D Aᵢ` and construct
`H = A₀ ⊗ 1 + ∑ᵢ Aᵢ ⊗ sᵢ`. For
`m(z) = (id ⊗ τ)((z-H)⁻¹)`, prove the Dyson equation

`m(z)⁻¹ = zI - A₀ - η(m(z))`.

Establish upper-half-plane properties, positivity and invertibility in the real
exterior resolvent domain, and the physical solution branch. Construct entrywise
semicircular models and prove their covariance and resolvent agree with the
corresponding reduced semicircular model.

## 5. Spectral-edge variational formulas

For a self-adjoint matrix-valued semicircular pencil and `b = sup spec(H)`, prove

`b = inf_{Z ≻ 0} λmax(A₀ + Z + ∑ᵢ Aᵢ Z⁻¹ Aᵢ)`.

Derive positive-state and density-matrix inequalities, positivity and spectral
bounds for `m(z)` when `z > b`, exterior differentiability, and the Lyapunov
identities obtained by differentiating the Dyson equation. Prove quantitative
finite-depth Fock approximations and positivity certificates as `z ↓ b`, including
singular limits and deterministic edge subspaces. Coefficients are general bounded
Hermitian coefficients; do not impose positivity or commutativity on them.

## 6. Spectral distributions and analytic transforms

For self-adjoint elements in faithful tracial C-star probability spaces, construct
compactly supported spectral probability measures and prove
`τ(f(a)) = ∫ f(x) dμₐ(x)` for continuous functional calculus. Establish support–spectrum
identification and
`Gₐ(z) = τ((z-a)⁻¹) = ∫ (z-x)⁻¹ dμₐ(x)`.
Reuse moment transforms, local inverses, and S-transforms. Prove compatibility of
algebraic distributions, moment convergence, and analytic transforms under explicit
boundedness assumptions.

## 7. Free multiplicative convolution and projection products

For free bounded positive `a,b`, define convolution through the law of
`a^{1/2} b a^{1/2}` and prove the analytic-germ identity
`S_{a^{1/2}ba^{1/2}} = Sₐ S_b` under nonzero first-moment assumptions.
For a projection of trace `α`, prove
`μₚ = (1-α)δ₀ + αδ₁` and `Sₚ(z) = (1+z)/(α+z)`.

For `L ≥ 2` free projections of trace one half, characterize their multiplicative
product law and prove its right spectral edge is
`λ_L = L^L / (2^L (L-1)^{L-1})`. Establish the exterior parameterization
`z_L(w) = (w+1/2)^L / (w(1+w)^{L-1})`, the physical branch, and the connection
between its critical point and actual spectral support. A formal critical-point
calculation does not establish the spectral-edge theorem.

## 8. Conditional multiplicative free subordination

Develop conditional expectations in tracial operator algebras as noncommutative
L² orthogonal projections. For bounded positive `A,T`, a von Neumann subalgebra
`B` containing `T`, and `A` free from the **entire algebra B**, prove

`E_B[A(z-TA)⁻¹] = (χ_T(w)⁻¹ - T)⁻¹`,

where `w = zG_{μ_A ⊠ μ_T}(z)-1`. Specify the inverse moment transform's physical
branch, nondegeneracy, and domains; prove the identity on an analytic domain before
extending to the positive exterior region. Prove compatibility with enlarged
conditioning algebras. For a projection `K ∈ B` with `KT = TK = 0` and `τ(K) > 0`,
provide the reusable specialization
`τ(KA(z-TA)⁻¹)/τ(K) = χ_T(w)` whenever the expressions are defined.

## 9. Haar freeness and asymptotic interfaces

Define Haar unitaries by their star-moments and prove free Haar conjugation,
including freely independent copies of a deterministic subalgebra. Develop joint
asymptotic freeness for independent Haar orthogonal matrices and independent
uniformly bounded families with convergent joint star-moments. Explicitly separate
expected normalized traces, convergence in probability, almost-sure moment
convergence, and strong convergence/spectral inclusion. State deterministic versus
random hypotheses, independence, and norm bounds. General orthogonal integration
and pairing combinatorics are separate dependencies; expected moments alone do
not prove almost-sure convergence.

## 10. Free Gaussian Ornstein–Uhlenbeck analysis

Construct Wick words with `τ(W_u* W_v) = δ_{u,v}`, multiplication/contraction
formulas, and operator-norm bounds. Construct `P_t(W_w) = exp(-t|w|) W_w` and prove
its semigroup law, complete positivity, unitality, trace preservation, normal
extension, and contractive noncommutative L² and L¹ extensions. Give explicit
positive decompositions of `P_t(FF*)` for finite matrix-valued Wick amplitudes.

Develop noncommutative integration and entropy to prove, for positive
`X ∈ L¹(M_N ⊗ M)`, `q = (Tr_N ⊗ τ)(X)`, `ρ = (id ⊗ τ)(X)`, and `t > 0`,

`D((id ⊗ P_t)X ‖ ρ ⊗ 1) ≤ q K_{r,t}`,

with finite `K_{r,t}` independent of matrix size and input Wick degree. Prove normal
relative-entropy data processing and lower semicontinuity. Start with bounded
finite Wick amplitudes, then extend to all positive L¹ inputs.

## 11. Independent follow-up milestones

Free products and positive free realizations; additive convolution and R-transform
additivity; the free central limit theorem; operator-valued cumulants and
amalgamated Wick formulas; second-order freeness and annular noncrossing
combinatorics; genus expansions and second-order Gaussian trace formulas; further
operator-valued subordination and spectral support.

## Priorities, verification, and completion

1. Cumulant calculus, full Fock systems, Wick formulas, integration by parts, Dyson.
2. Spectral measures, edge certificates, multiplicative convolution, projection
   products, analytic subordination.
3. Haar conjugation and joint asymptotic freeness, with orthogonal integration.
4. Free Gaussian OU, noncommutative Lᵖ, and conditional entropy regularization.

Independent modules may be developed in parallel after agreeing on interfaces and
mathematical assumptions; use separate worktrees and focused branches.
Preserve public interfaces and separate algebraic, combinatorial, analytic,
operator-valued, and asymptotic modules. State positivity, faithfulness, traciality,
normality, boundedness, and domains explicitly. Separate formal series from
analytic identities and moment convergence from norm convergence.

Every completed theorem must be genuinely kernel-checked, without placeholders,
new mathematical axioms, bypasses, circular assumptions, or weakened targets.
Add meaningful usage examples. Run the complete build, integrity guard, and
transitive axiom audit before declaring milestones verified. Follow
[AGENTS.md](../AGENTS.md) for committing, publishing, and integration.
Record exact missing dependencies in [PROGRESS.md](../PROGRESS.md) and
[DEPENDENCIES.md](DEPENDENCIES.md), and continue with useful intermediate results.

Success means semicircular resolvent identities, spectral-edge formulas,
projection-product laws, conditional subordination, Haar freeness, and OU estimates
are established reusable theorems. Supporting special cases and conditional
statements do not complete those targets.
