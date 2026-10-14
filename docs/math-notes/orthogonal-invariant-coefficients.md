# Actual invariant coefficient laws and fresh-color rotation

Verified milestones on `feat/compact-haar-averaging`:

- `2ffa088`, `RandomMatrix/OrthogonalInvariantCoefficients.lean`.
- `ea68470`, `RandomMatrix/OrthogonalInvariantRotation.lean`.

Both depend on the frozen actual tensor and pairing Gram/independence chain.
Goal certification and integration remain coordinator responsibilities.

## Genuine all-order coefficient laws

The premises are ACTUAL fixedness in `tensorPowerRepresentation.fixedVectors`,
not assumed scalar coefficient relations. The statements apply to all tensor
orders and all finite coordinate types, including degenerate cases.

`tensorPower_reflection_coefficient` proves the genuine reflection action is
multiplication by (-1) raised to the color multiplicity. Consequently
`invariantTensor_coefficient_eq_zero_of_odd_count` proves vanishing whenever any
color appears an odd number of times.

`tensorPower_permutation_coefficient` proves the actual permutation action
relabels the entire tuple. `invariantTensor_permutation` therefore derives
coefficient invariance under arbitrary coordinate permutations.

`invariantTensor_planeMixer` gives the literal full tuple-sum identity for the
actual normalized plane mixer with inverse-square-root-of-two entries. This is
an actual orthogonal matrix, not an assumed scalar rotation equation.

## Exact fresh-color splitting recurrence

`ColorSites i c` is the actual finite subtype of sites with color c.
`colorSplitTuple i c d gamma` replaces each such site by c or d according to its
Boolean choice, leaving all other sites unchanged. `colorSplitEquiv` proves a
GENUINE finite equivalence between these Boolean choices and ALL allowed tuple
labels in the nonzero mixer kernel.

For distinct c,d with d absent from the original tuple, the actual kernel product
is q^m on this precise support and zero elsewhere, where q = 1/sqrt(2) and m is
the number of c-colored sites. The finite support equivalence converts the actual
tensor action into the complete split sum.

`invariantTensor_fresh_color_split` proves
v(i) = q^m * sum over ALL gamma : ColorSites i c -> Bool of v(colorSplitTuple gamma).
The recurrence is DERIVED from actual fixedness, exact normalized matrix entries
and full tuple enumeration. It assumes neither a recurrence, a pairing expansion,
invariant-tensor spanning nor a generic dimension bound. Fresh-color availability
is an explicit hypothesis of this particular splitting statement.

## Verification and remaining spanning frontier

Both focused modules compile warning free under the shared lock. Principal
statements passed transitive standard-logic audits; exact normalized plane and
fresh-color recurrence statements were inspected. Integrity guard and staged
diff checks passed before atomic commits, all immediately pushed.

Failed elaborations concerned matrix identity coercions, dependent finite-choice
support rewriting and `Finset.subtype_univ` normalization. Statements were not
weakened and no coefficient relation was added as a premise.

The stable-dimension FIRST FUNDAMENTAL THEOREM is still unproved. A next route is
actual residual vanishing: if coefficients on all distinct-color pair-block tuples
vanish, reflect away odd counts and use a fresh color to split a block of even
size at least four. Proper splits use MORE colors and should vanish by induction;
unsplit endpoints have equal coefficients by genuine permutation invariance.
Since 2*q^m < 1 for m >= 4, the original coefficient then vanishes. The needed
support-cardinality induction, pair-block realization, residual subtraction and
span identification remain obligations. All-dimension spanning and general
low-dimensional pseudoinverse integration remain additional distinct obligations.
No general Weingarten formula or joint asymptotic freeness is claimed here.
