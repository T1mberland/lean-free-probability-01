# Actual vacuum grading and whole-double-commutant OU composition

This checkpoint proves the additive-time law for the actual intrinsic unital CP
OU maps on the whole literal orthonormal-family double commutant. The proof uses
actual full Fock grading and faithful vacuum separation. It assumes neither
polynomial norm density in the von Neumann algebra nor a WOT-closure/double-
commutant equivalence nor an ambient all-bounded-operator semigroup law.

## Verified mathematical chain

1. `4100d2b`, `OrnsteinUhlenbeckVonNeumannVacuumSandwich.lean`:
   `ouVacuumSandwich r s hrs` is the actual bounded Hilbert-space operator
   `Γ(first)† Γ(rotation) Γ(first)` on the literal completed tensor Fock space.
   It fixes the vacuum and satisfies
   `A(Cre(h)f) = r • Cre(h)(Af)` for every completed vector. Thus its actual
   creator-word vacuum image has eigenvalue `r^length`.
2. `7b7ba14`, `OrnsteinUhlenbeckVonNeumannVacuumDamping.lean`:
   `ou_fullTensorWord_creatorVacuum` identifies every full Hilbert-basis word
   under the existing onto tensor unitary with its actual creator-word vacuum
   vector. The completed `lp.ext_continuousLinearMap` theorem then proves
   `ouVacuumSandwich_eq_degreeDamping` on ALL Fock vectors at nonnegative time.
   No finite-dimensional or countability assumption on the original Hilbert
   space is used.
3. `05cdeaf`, `OrnsteinUhlenbeckVonNeumannVacuumIntertwining.lean`:
   the actual prefix embedding intertwines EVERY bounded source operator with
   `Γ(first)`. Rotations fix the vacuum. Consequently
   `ouDoubleCommutantTimeCP_vacuum_vector` proves
   `P_t(T) Ω = D_t(T Ω)` for EVERY bounded tensor-Fock operator. The exact
   intrinsic wrapper holds on the whole double commutant of any prescribed
   field family.
4. `bc3c599`, `OrnsteinUhlenbeckVonNeumannVacuumSemigroup.lean`:
   the independently verified faithful vacuum state for an orthonormal family
   makes the actual vacuum separating on its literal double commutant.
   `ouVonNeumannTimeCP_add` proves
   `P_t(P_u(T)) = P_(t+u)(T)` for EVERY element of that algebra, using only the
   all-operator vacuum identity, degree-damping composition, proved intrinsic
   range, and separation. `ouVonNeumannTimeContinuous_add` is the actual bounded
   linear composition identity on the complete intrinsic C-star algebra.
5. `022296d`, `OrnsteinUhlenbeckVonNeumannVacuumL2.lean`:
   genuine bounded vacuum evaluation on the whole double commutant is injective
   for an orthonormal family. The actual state satisfies `τ(T* T)=‖TΩ‖²`, and
   `ouVonNeumannTimeCP_state_L2_le` proves its true L2 quadratic contraction.
   `ouVonNeumannTimeCP_vacuum_strong_continuous` proves norm-strong time
   continuity of every actual vacuum image, including time zero. The quadratic
   inequality and vacuum-image continuity need no orthonormality assumption.

The orthonormal family need not span the one-particle Hilbert space. These
results never identify its cyclic L2 Hilbert space with all ambient Fock space.

## Verification and persistent design decisions

All five final focused builds completed with exit code zero under the common
build lock. Eighteen principal direct axiom audits completed with exit code zero
and depended only on `propext`, `Classical.choice`, and `Quot.sound`.
Proof-source integrity and whitespace diff checks passed. Every atomic source
commit was pushed successfully before subsequent development. All earlier
intrinsic, ambient, finite-rank, and faithfulness source modules were preserved.

The all-vector sandwich proof uses the previously proved strong creator
pull-through rather than inventing an adjoint formula for recursive completed
tensor maps. Equality on full basis-word singleton maps extends directly to the
complete Hilbert sum. Scalar-singleton equality is proved coordinatewise to
avoid an elaboration mismatch between distinct decidable-equality instances.

The family double-commutant semigroup law follows from vacuum separation rather
than a finite-rank approximation of arbitrary operators. The separate bounded
finite-word approximation remains valid and useful, but an ambient all-operator
semigroup law is not needed or proved by this chain.

## Exact remaining scope

The underlying maps are genuine intrinsic unital CP contractions, preserve the
actual vacuum state, have time-zero identity, and satisfy additive composition
on the literal orthonormal-family double commutant. They are continuous on its
concrete WOT uniform norm balls by the earlier intrinsic WOT checkpoint.

Preservation of bounded increasing positive suprema (normality) is NOT proved
here. Neither global WOT continuity on unbounded nets nor a normal extension
interface is inferred from the bounded-WOT result. Strong time continuity here
is specifically continuity of vacuum images in Hilbert norm; operator-norm time
continuity on the whole double commutant is not asserted.

An independently constructed complete cyclic/GNS L2 extension, intrinsic L1
extension, hypercontractivity, logarithmic Sobolev inequalities, and entropy
results remain distinct obligations. The earlier native generated C-star cyclic
L2 construction is not silently identified with a new whole-von-Neumann GNS
completion by this checkpoint.
