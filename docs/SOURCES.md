# Public sources and attribution

## Mathlib

The project uses [mathlib](https://github.com/leanprover-community/mathlib4) at
revision [`d13f23b723b8a846827a245b89c10fc7d3f11612`](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612),
with Lean 4.34.1. The manifest and toolchain files pin the dependencies.

## Existing unitary Weingarten formalization

[T1mberland/lean-weingarten](https://github.com/T1mberland/lean-weingarten),
inspected at revision
[`e3a09fdfaeeab526388990a52b9911dd8e955ab2`](https://github.com/T1mberland/lean-weingarten/tree/e3a09fdfaeeab526388990a52b9911dd8e955ab2),
contains unitary Haar integration and coefficient-decay results on Lean/mathlib
4.28.0. It is a reuse candidate and has not been added as a project dependency.
Reuse requires a verified port or compatible interface. Orthogonal integration
also needs its own pairing combinatorics.

The compact-group Haar normalization and uniqueness proof pattern has been
adapted and checked for real orthogonal matrices here, with attribution and the
originating Apache 2.0 license retained in
[OrthogonalHaar.lean](../FreeProbability/RandomMatrix/OrthogonalHaar.lean).

## Interface checks

An inverse moment transform requires a nonzero first moment. The library makes
that domain explicit in
[Transform.lean](../FreeProbability/Analytic/Transform.lean).

Mathlib's additive Haar disintegration under linear maps does not itself supply
a conditional orthogonal-group fiber law. Such a result needs a separate proof
when an application requires it.
