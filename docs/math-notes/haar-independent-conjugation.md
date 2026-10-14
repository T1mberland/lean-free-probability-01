# Entire copies under independent Haar conjugators

Published mathematical milestone `72099e9`:
`FreeProbability/Algebraic/HaarIndependentConjugation.lean`, on
`feat/haar-conjugation`, depending on the frozen abstract Haar core through
`2ff26dd` and its notes `be814c9`.

## Exact theorem scope

`freelyIndependent_independentHaarConjugatedAlgebras` applies to ANY index type I,
including infinite and empty types. Given actual unitaries u_i in a unital star
algebra with a normalized field-valued linear expectation, it assumes:

1. Each u_i is Haar through its complete nonzero integer-power moment condition.
2. The ORIGINAL family indexed by `Unit ⊕ I`, consisting of the ENTIRE base
   subalgebra B and each ENTIRE Haar-generated star algebra, is JOINTLY freely
   independent.

It proves that the ENTIRE actual image algebras u_i B u_i* are freely independent.
There are no trace, positivity, topological, completeness or finiteness assumptions.
The joint original hypothesis is not replaced by pairwise freeness, generator-only
moment checks, or pairwise distinctness of all labels in a word.

## Mathematical proof

A complete alternating product of centered conjugated preimages expands into the
actual letters u_i, b_i, u_i*. Each conjugator and its adjoint belongs to its entire
Haar-generated algebra and is centered. Adjacent different original indices keep
the neighboring u_i* and u_j in DIFFERENT algebras. Nonadjacent repeated indices
are permitted. The expanded word is nonempty, genuinely alternating and centered,
so ORIGINAL JOINT freeness annihilates its expectation.

`haarIndependentBaseFamily_pair_free` is an injective reindexing of the original
full joint hypothesis. It supplies each full B/Haar pair and the already proved
trace-free expectation preservation of conjugation. Applying the actual inverse
star-algebra automorphism to every centered image element recovers a centered
preimage in B; this upgrades the word lemma to the full subalgebra-image theorem.

## Verification and remaining frontier

The focused module compiles warning free. Five important declarations passed
transitive standard-logic audits, including the full arbitrary-I statement.
Source-integrity guard and staged diff checks passed; the atomic commit was pushed
immediately. Failed elaborations concerned sum-constructor disjointness, explicit
first-power reduction, generated-family unfolding, and a composed-map rewrite;
all were repaired without changing hypotheses or conclusions.

This is a genuine abstract algebraic conjugation theorem. It does not construct
universal free Haar realizations or prove finite Haar orthogonal asymptotic
freeness. General higher Haar integration/pairing estimates, joint asymptotic
freeness, convergence in probability, almost-sure moments and strong convergence
remain distinct obligations. Existing actual orthogonal first/second/fourth moment
and sphere-law developments are independent tools, not asserted substitutes for
the unproved general integration theorem. Integration and goal certification are
coordinator responsibilities.
