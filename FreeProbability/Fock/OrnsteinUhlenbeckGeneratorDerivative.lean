import FreeProbability.Fock.OrnsteinUhlenbeckGeneratorError

/-! Actual strong right-sided difference-quotient derivative on the exact number-operator domain. -/
noncomputable section
open scoped Classical InnerProductSpace Topology
open Filter
namespace FreeProbability.Fock
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A total real-time function using only the actual nonnegative-time bounded degree maps.
At negative times it equals time zero; the derivative theorem uses right-sided time only. -/
def ouGeneratorDamping (t : ℝ) : TensorFullFock H →L[ℂ] TensorFullFock H :=
  degreeDamping H (max t 0) (le_max_right t 0)

 theorem ouGeneratorDamping_nonneg (t : ℝ) (ht : 0 ≤ t) :
    ouGeneratorDamping H t = degreeDamping H t ht := by
  simp only [ouGeneratorDamping, max_eq_left ht]

/-- Exact agreement of the constructed complete error vector with the genuine OU difference quotient. -/
theorem ouGeneratorError_eq_quotient (f : numberOperatorDomain H) (t : ℝ) (ht : 0 ≤ t) :
    ouGeneratorError H f t = (t⁻¹ : ℂ) •
      (ouGeneratorDamping H t (f : TensorFullFock H) - (f : TensorFullFock H)) + numberOperator H f := by
  apply lp.ext
  funext n
  change (ouGeneratorScalarError n (max t 0) : ℂ) • (f : TensorFullFock H) n =
    (t⁻¹ : ℂ) • (ouGeneratorDamping H t (f : TensorFullFock H) n - (f : TensorFullFock H) n) +
      (n : ℂ) • (f : TensorFullFock H) n
  rw [ouGeneratorDamping_nonneg H t ht, degreeDamping_degree]
  simp only [max_eq_left ht, ouGeneratorScalarError, degreeWeight]
  push_cast
  simp only [div_eq_mul_inv]
  module

/-- Genuine Hilbert-norm right derivative of actual degree damping at zero, for EVERY true-domain vector. -/
theorem ouGenerator_right_tendsto (f : numberOperatorDomain H) :
    Tendsto (fun t : ℝ => (t⁻¹ : ℂ) •
      (ouGeneratorDamping H t (f : TensorFullFock H) - (f : TensorFullFock H)))
      (𝓝[>] (0 : ℝ)) (𝓝 (-numberOperator H f)) := by
  have ht : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have h := (ouGeneratorError_tendsto H f).sub (tendsto_const_nhds (x := numberOperator H f))
  have he : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      ouGeneratorError H f t - numberOperator H f = (t⁻¹ : ℂ) •
        (ouGeneratorDamping H t (f : TensorFullFock H) - (f : TensorFullFock H)) :=
    ht.mono (fun t h => by rw [ouGeneratorError_eq_quotient H f t h.le, add_sub_cancel_right])
  simpa only [zero_sub] using h.congr' he

end FreeProbability.Fock
