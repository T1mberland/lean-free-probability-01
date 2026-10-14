# The actual Fock number operator and its exact domain

The construction is on `TensorFullFock H`, the genuine complete infinite
Hilbert sum of recursively completed tensor powers of any complete complex
Hilbert space. No basis cardinality, spanning, or nontriviality hypothesis is
added. The one-particle space may be zero.

## Verified milestones

- `2f27890`, `OrnsteinUhlenbeckNumberOperatorDomain.lean`:
  `numberOperatorDomain H` is exactly the submodule
  `{f | Memℓp (fun n => (n:ℂ) • f n) 2}`.
  `numberOperator H` is an actual domain-restricted linear map into complete
  Fock space, with degree coordinate `n • f_n`. Every pure completed tensor
  degree belongs to this domain and has the literal expected number image.
- `022b0f7`, `OrnsteinUhlenbeckNumberOperatorSymmetry.lean`:
  unconditional finite-grade singleton sums prove that this actual operator
  domain is dense in complete Fock space. `numberOperator_inner_symmetric`
  proves true symmetry on the specified domain, and
  `numberOperator_quadratic_nonneg` proves actual nonnegative quadratic form.
- `430478d`, `OrnsteinUhlenbeckNumberOperatorDamping.lean`:
  actual degree damping preserves precisely that operator domain. The true
  restricted domain semigroup is constructed, `N D_t f = D_t N f` is proved,
  and the actual number-image norm is contractive.
- `a9ecf5a`, `OrnsteinUhlenbeckNumberOperatorAdjointDomain.lean`:
  testing the weak-adjoint identity in each completed tensor grade forces
  `z_n = n y_n`. Square summability of the actual vector `z` then forces
  `y` into the exact weighted operator domain. The precise theorem is

  `(∀ f : Dom(N), ⟪Nf,y⟫ = ⟪f,z⟫) ↔ ∃ g : Dom(N), g=y ∧ Ng=z`.

  Thus the full weak-adjoint graph is exactly the actual operator graph,
  beyond the earlier symmetry result. No larger assumed adjoint domain or
  unverified generic unbounded-operator class is introduced.
- `f1f3946`, `OrnsteinUhlenbeckNumberOperatorClosedGraph.lean`:
  the actual graph is the intersection of its closed weak-adjoint coefficient
  equations. It is norm-closed in the product of completed Fock spaces.
  Any convergent graph net has its actual limit in the same weighted domain
  with the expected number image.

## Domain distinctions

The operator domain requires square summability after multiplying each degree
by `n`, equivalently the usual weighted squared norm sum with weight `n²`.
It is not the quadratic-form domain, which naturally requires weight `n` in the
squared norm sum. No identification of those distinct domains is claimed.

The number operator is given as a linear map from its proper specified domain,
not as a continuous linear map on all ambient vectors. No blanket proof of
unboundedness is asserted for all `H`: for a zero one-particle space the positive
tensor levels vanish, so the number operator can be zero. The exact adjoint-graph
and closedness results above hold uniformly, including that case.

## Verification and implementation decisions

All five final focused builds completed with exit code zero under the shared
build lock. Eighteen principal direct axiom audits completed with exit code zero
and depended only on `propext`, `Classical.choice`, and `Quot.sound`.
Proof-source integrity and whitespace diff checks passed. Every mathematical
commit was pushed successfully before further development. Earlier frozen
symmetry, intrinsic OU, ambient dilation, and tensor sources were preserved.

Dependent coordinate functions explicitly annotate their index as `ℕ`; writing
an untyped `(n:ℂ)` prematurely infers a complex index. Membership conversions
between the `PreLp` function synonym and dependent functions are justified by
coordinate extensionality. The true domain closure and scalar properties use
actual `Memℓp` addition and constant scalar multiplication.

## Remaining obligations

The exact graph criterion is verified directly; a separately packaged generic
unbounded self-adjoint operator interface is not introduced. No semigroup
infinitesimal differentiation theorem is claimed merely from grade action.
A genuine generator proof must show a norm limit of difference quotients on the
specified weighted operator domain. At time zero this should use the right-sided
nonnegative-time domain, since exponential weights at negative time do not
produce a bounded damping map on arbitrary Fock vectors.

A true closed quadratic-form package on the distinct form domain, faithful
whole-von-Neumann GNS/cyclic L2 identification, order-supremum normality of OU,
intrinsic L1 extension, hypercontractivity, logarithmic Sobolev inequalities and
entropy results remain separate obligations. A bounded inverse for `N+1` may
provide a useful independent next operator-domain milestone.
