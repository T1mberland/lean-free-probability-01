# Bounded finite-word approximation

This checkpoint constructs finite-rank approximations on the complete word
Fock space and transfers them to the literal infinite Hilbert sum of recursively
completed tensor powers. The alphabet is arbitrary; neither countability nor
nonemptiness is assumed.

## Verified source milestones

- `6bd59b3`: `OrnsteinUhlenbeckVonNeumannFiniteRankProjection.lean`.
  `finiteWordProjection S` keeps exactly the coordinates in the finite set
  `S : Finset (List I)`. It is self-adjoint and idempotent, with operator norm
  at most one. Its exact value is the finite sum of coordinate singletons.
  `finiteWordProjection_mem_span` and `finiteWordProjection_finite_span`
  prove that its range lies in an actual finite-dimensional word span.
- `6e26d36`: `OrnsteinUhlenbeckVonNeumannFiniteRankApproximation.lean`.
  `finiteWordProjection_tendsto` proves strong convergence to the identity
  along `atTop` on all finite word sets, using the actual unconditional
  `lp.hasSum_single` theorem. `finiteWordSandwich S T` is exactly
  `F_S ∘ T ∘ F_S`, has finite-dimensional range, and satisfies
  `norm_finiteWordSandwich_le : ‖F_S T F_S‖ ≤ ‖T‖` for every bounded operator.
  `finiteWordSandwich_tendsto_WOT` proves convergence to that same operator
  in the genuine weak operator topology.
- `e1dae64`: `OrnsteinUhlenbeckVonNeumannFiniteRankTensor.lean`.
  The actual unitary `fullFockTensorDecomposition H` transports these operators
  to `TensorFullFock H`. The tensor projection is self-adjoint and contractive,
  and converges strongly to the identity. The tensor sandwich is proved equal
  to literal projection composition, has range in a proven finite-dimensional
  transported word span, has the same uniform norm bound, and converges in WOT
  to every bounded tensor Fock operator.

## Proof mechanism and verification

The norm bound for the projection is coordinatewise monotonicity of the
complete ℓ² norm. Its adjoint identity follows from the coordinate inner-product
sum. A sandwich coefficient is exactly

`⟪y, F_S T F_S x⟫ = ⟪F_S y, T(F_S x)⟫`.

Strong convergence of both vectors and boundedness of `T` give convergence of
this coefficient. The pinned WOT coefficient characterization then supplies
operator convergence. The tensor result uses the previously constructed onto
Hilbert unitary, not an algebraic tensor-space surrogate.

Each final focused module build completed with exit code zero under the common
build lock. Direct audits of the principal declarations completed with exit
code zero and used only `propext`, `Classical.choice`, and `Quot.sound`.
The repository proof-source integrity guard and whitespace diff checks passed.
Each atomic source commit was pushed successfully before subsequent work.

## Remaining obligations

These finite-word projections approximate every bounded operator. They are not
claimed to belong to a prescribed semicircular von Neumann algebra. No
Kaplansky density theorem or equivalence between a WOT closure and a literal
double centralizer is assumed or derived here.

To extend the actual ambient OU semigroup law by this approximation, one must
still prove the exact OU image of each word matrix unit (including the vacuum
projection correction), establish composition on their finite spans, and use
the already proved continuity on uniform norm balls. The finite-rank
approximation alone does not prove that semigroup law.

Order-supremum normality, an intrinsic normal von Neumann OU extension,
L¹ extensions, hypercontractivity, logarithmic Sobolev inequalities, and entropy
results remain distinct mathematical obligations. Infinite amplification is not
asserted globally WOT-continuous on unbounded nets.
