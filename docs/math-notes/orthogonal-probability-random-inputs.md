# Actual probability modes and independent random input extension

Published checkpoints on `feat/orthogonal-probability-random-inputs`, based on
frozen actual multitrace convergence checkpoint `47a84dd`:

- `2ed976b`: `OrthogonalMultiTraceProbability.lean`.
- `bdfb597`: `OrthogonalMultiTraceProbabilityRandomInputsBounds.lean`.
- `3ca50f9`: `OrthogonalMultiTraceProbabilityRandomInputs.lean`.
- `086d4b9`: `OrthogonalMultiTraceProbabilityIndependentInputs.lean`.
- `909a458`: `OrthogonalMultiTraceProbabilityRandomInputsConvergence.lean`.
- `7bec383`: `OrthogonalMultiTraceProbabilityRandomInputsMarginals.lean`.

All previous sources are unchanged and frozen. This note supersedes the open
probability/countable/random-input interfaces in the earlier convergence notes.

## Deterministic inputs: actual probability and simultaneous words

`probabilityMeasure_of_haar_marginal` derives that the common source measure
is a probability measure from an actual measure-preserving normalized Haar
marginal. No additional finiteness or probability hypothesis is needed.
`centered_traceWord_tendstoInMeasure` proves actual convergence in probability
from the already proved actual almost sure theorem and genuine measurability.

`ae_countable_centered_traceWords_tendsto` proves one common full-measure
set for a countable collection of fixed centered trace words. Degrees and
operator bounds may vary across the collection. No uncountable intersection
or global bound over the collection is assumed.

## Genuine pointwise bounds and random observables

Complexification of an actual real orthogonal matrix is proved to be genuinely
unitary. Actual normalized complex trace is contractive for the literal
Euclidean operator norm, with dimension zero handled by the project's zero
normalization. Actual unitary conjugation and the ordered matrix product give

```
|traceWord(A,B,U)| ≤ (∏k ||toEuclideanCLM(A_k)||)
                         (∏k ||toEuclideanCLM(B_k)||)
                   ≤ K^(2r),  r>0.
```

This pointwise statement requires no centering or integration. The actual trace
polynomial is jointly continuous and measurable in both entire deterministic
words and the actual orthogonal matrix. Genuine random-input measurability is
derived from measurable data maps rather than assumed for the final observable.

## Actual product law and Fubini

For any input probability measure ν and measurable matrix word maps A/B,
`randomInputsTraceWordSecondMoment` is the actual Bochner squared-norm integral
against ν times actual normalized compact orthogonal Haar measure. Actual
almost-everywhere Euclidean operator bounds yield integrability from the
pointwise scalar bound; integrability is not an extra premise.

`randomInputsTraceWordSecondMoment_eq_integral` proves the genuine Fubini
identity with the ν-integral of actual Haar second moments. Actual marginal
centering and operator bounds, imposed only ν-almost everywhere, give the
true eventual bound C_(2r) K^(4r) N^-2. This is an actual product-law calculation,
not an assumed conditional expectation identity.

## Arbitrary independent random realizations

For input data Y and an orthogonal random matrix X on a common source space,
`independent_inputs_haar_measurePreserving` proves that actual `IndepFun Y X μ`
and the actual Haar marginal imply their actual joint law is
`(μ.map Y) × Haar`. The source probability measure is derived from the Haar
marginal. Matrix factors inside the data tuple need not be independent.

The actual squared-norm integral and its integrability transfer through this
measure-preserving pair. `eventually_independent_inputs_traceWordSecondMoment_bound`
has ONE degree-dependent dimension threshold followed by ALL input laws and
realizations. This order of quantifiers permits Y_N to have a different law
in each dimension; it does not incorrectly apply a fixed-law tail to varying laws.

`ae_independent_inputs_traceWord_tendsto` and
`independent_inputs_traceWord_tendstoInMeasure` prove actual almost sure and
probability convergence for these centered uniformly bounded random inputs.
No independence between dimensions is required. The public generic Tonelli
lemma `ae_tendsto_zero_of_summable_integral_norm_sq` proves the required
almost sure implication for any normed additive group from summable actual
second absolute moments.

## Natural source hypotheses and countable random words

Measurable finite-word trace-zero events and literal Euclidean operator-bound
events are constructed explicitly. Thus `ae_centered_inputs_map_iff` and
`ae_bounded_inputs_map_iff` identify marginal-almost-everywhere hypotheses
with their actual source-almost-everywhere counterparts. These are not added
or stronger distributional assumptions.

The `_of_source` wrappers state centering and bounds directly on the original
random realization. The countable source wrapper proves one full-measure set
for countably many random input words, with individual positive lengths and
bounds, dimension-dependent input laws, and no independence across dimensions.

## Verification and resolved engineering issues

Focused builds passed warning-free with explicit exit zero: 3052, 3054, 3055,
3056, 3057, and 3058 jobs. All 3, 7, 5, 4, 3, and 5 public declarations
respectively were directly transitively audited with only `propext`,
`Classical.choice`, and `Quot.sound`. Source integrity and whitespace/diff
checks passed, and every atomic commit was immediately pushed successfully.

The matrix measurable-space and complex Borel-space imports were already
cached at the pinned revision. A broad continuous-to-measurable conversion
for whole finite matrix words encountered a deterministic elaboration timeout.
It was replaced by exact measurable matrix-entry sums and a finite ordered
product induction; no heartbeat increase or weakened mathematical input was
used. Later applications needed explicit site/color types to avoid unknown
matrix-type inference. Fubini normalization used the actual probability
measure identity, and actual measure-map equality was rewritten explicitly
when transferring the Bochner integral.

## Remaining mathematical scope

This chain proves the centered alternating normalized-trace criterion for ONE
Haar conjugation against arbitrary independent uniformly bounded random matrix
inputs. Marginal convergence is not needed for this centered criterion; full
joint-law packaging with convergent marginal star-moments is still separate.

Finite independent Haar colors next need actual product-law entry integration
and color-respecting pairing/trace interfaces. Low-dimensional full orthogonal
integration and strong convergence/spectral inclusion remain separate goals.
No joint multicolor asymptotic-freeness or strong-convergence theorem is claimed
here. Integration and goal certification remain coordinator responsibilities.
