# Arbitrary CP covariance Gram positivity

Source milestone `aace45c` proves actual finite C-star Gram positivity,
cp_covariance_gram_nonneg and cp_covariance_quadratic_nonneg for every
completely positive covariance on an arbitrary unital ordered C-star algebra.
The finite index type may be empty. Nonempty is only an internal proof split;
no unitality, finite Kraus form, trace or faithfulness premise is added to covariance.

For nonempty index sets a single nonzero matrix row realizes the actual Gram
as star R * R. CP sends that genuine positive matrix to a positive C-star matrix.
A matrix star square has coefficient quadratic form equal to
sum_k star(sum_i Y_ki b_i) * (sum_j Y_kj b_j), with the noncommutative order intact.
Induction over the additive positive cone extends to every positive matrix.

An initial single-square-factor approach hit missing matrix functional-calculus
instances in the focused import environment. The verified proof instead uses
StarOrderedRing.nonneg_iff and AddSubmonoid.closure_induction, removing that
unneeded CFC dependency and preserving the intended generality. Initial broad
simp unfolded matrix representations too early; an explicit ordered-entry change
resolves that engineering problem. No resource limit or kernel mechanism changed.

This is the positivity prerequisite for a general CP correspondence construction,
not a realization theorem. Remaining mathematical infrastructure includes
algebraic B-valued correspondence, nullspace quotient and completion, bounded
left action, balanced completed tensor powers, adjointable operators, full
module Fock space and genuine CP vacuum expectation. Ordered noncrossing Wick
recursion can be proved independently as an algebraic conditional result.
