# Actual cyclic Hilbert L² extension of the native OU semigroup

This checkpoint extends the genuine native C-star OU self-map to its actual
complete cyclic Hilbert representation. It does not identify a nonspanning
family's cyclic space with the entire tensor Fock space.

## Degree damping on genuine complete tensor Fock space

`degreeDamping H t ht` acts on `TensorFullFock H`, the actual infinite Hilbert
sum of recursively completed tensor powers. Its degree-n multiplier is
`degreeWeight t n = (Real.exp (-t):ℂ)^n`. For `t ≥ 0`, each scalar norm is at
most one. `Memℓp.mono'` proves summability for every infinite input vector, and
`lp.norm_mono` proves genuine Hilbert norm contraction. The vacuum is fixed,
zero time is the identity, and additive time is actual composition.

Source checkpoint: `f8a6240`, `OrnsteinUhlenbeckL2Damping.lean`.

## Actual Wick vectors and vacuum implementation

`tensorWordVector w` is a literal recursively completed pure tensor of degree
`w.length`. Creation on elementary completed tensor sectors proves
`tensorCreatorWord w Ω = lp.single 2 w.length (tensorWordVector w)`.
Wick recursion and the canonical annihilation-creation relation cancel the
first contraction, proving the genuine recursive Wick polynomial has the
same vacuum vector. These statements hold for arbitrary vector words; an
orthonormality or totality assumption is not required for pure grading.

Thus degree damping has the exact OU eigenvalue on actual closed family Wick
vacuum vectors. Generic normed-target Wick density extends the identity to
every element of the native generated C-star closure:

`familyOUTime_vacuum_vector`: `OU_t(T)Ω = degreeDamping_t(TΩ)`.

This is an actual continuous-linear-map identity, not a finite polynomial-only
or scalar moment statement. It gives true vacuum norm contraction and hence
`familyOUTime_state_L2_le`, the real quadratic state inequality
`Re τ(OU_t(T)*OU_t(T)) ≤ Re τ(T*T)`. The proved state quadratic form is exactly
`τ(T*T) = (‖TΩ‖:ℂ)^2`; operator norm contraction was not substituted for the
state L² estimate.

Source checkpoints: `b586c84` pure completed Wick degrees; `570f486` actual
vacuum implementation and state L² contraction.

## Genuine complete cyclic Hilbert extension

`familyCyclicSpace e` is the closed complex submodule
`closure(range(familyVacuumVector e))` inside fixed completed tensor Fock space.
It inherits the actual Hilbert inner product and completeness from that closed
submodule. `familyCyclicVector` is the bounded native vacuum evaluation with
this codomain, and its range is proved dense.

The vacuum implementation shows damping maps every original vacuum vector to
another native OU vacuum vector. Continuity and closedness prove invariance
of the full cyclic closure. Restricting actual degree damping therefore gives
`familyOUL2 e he t ht`, a genuine bounded operator on the complete cyclic
Hilbert space. It is norm contractive, fixes the cyclic vacuum, satisfies
zero-time and additive-time laws, and agrees with the native OU self-map on
all native vacuum vectors. `familyOUL2_unique` proves uniqueness among bounded
extensions agreeing on that genuine dense orbit.

Source checkpoint: `e30ef66`, `OrnsteinUhlenbeckL2Cyclic.lean`.

## Verified scope and remaining obligations

All complete one-particle Hilbert spaces and arbitrary orthonormal families
are covered, without spanning, countability, dimension, or nontriviality
assumptions. The actual cyclic representation may be a proper subspace of full
Fock. No equality with full Fock is asserted. No unproved GNS-identification or
normal von Neumann extension is used.

Principal declarations passed focused common-lock Lean builds, transitive
axiom audits with only `propext`, `Classical.choice`, and `Quot.sound`, and the
project source-integrity guard. These are feature-branch source achievements;
the coordinator owns integration and persistent central ledgers.

Strong time continuity, L¹ extension, native embedding normality, normal OU
extension, hypercontractivity, logarithmic Sobolev estimates, and entropy
monotonicity remain separate mathematical obligations. The pinned library has
concrete WOT bounded-operator APIs but lacks a ready bicommutant/Kaplansky/
predual package. Actual WOT-continuity of ambient compression or conjugation
would not, by itself, prove the native included-algebra embedding is normal.
An additional genuine representation/embedding bridge is required.

Useful next tasks are strong time continuity of actual degree damping on the
Hilbert sum and its cyclic restriction, and separately WOT-continuity of
ambient isometry compression as honest normality groundwork.

## Implementation decisions and failed approaches

The pure Wick vacuum grading was proved directly from Wick recursion and
creation-annihilation contraction, avoiding an unnecessary orthonormal-basis
identification prerequisite. The closure invariance proof uses the actual
operator's closed-set preimage. An uncast `Submodule.range ⊆ Set` expression
failed elaboration; explicitly casting the range to its carrier set resolved
it. Preimage membership also required an explicit operator-application
`change` before rewriting the true vacuum implementation. No resource limits
were increased and no mathematical assumptions were weakened.
