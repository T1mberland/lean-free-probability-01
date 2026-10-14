import FreeProbability.Fock.OrnsteinUhlenbeckGeneratorDerivative

/-! Exact strong-generator domain: existence of the actual right quotient limit is equivalent
 to the genuine weighted-square-summability number-operator domain. -/
noncomputable section
open scoped Classical InnerProductSpace ENNReal Topology
open Filter
namespace FreeProbability.Fock
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual right OU quotient, defined for every ambient Fock vector. -/
def ouGeneratorQuotient (f : TensorFullFock H) (t : ℝ) : TensorFullFock H :=
  (t⁻¹ : ℂ) • (ouGeneratorDamping H t f - f)

 theorem ouGeneratorQuotient_degree_tendsto (f : TensorFullFock H) (n : ℕ) :
    Tendsto (fun t => ouGeneratorQuotient H f t n) (𝓝[>] (0 : ℝ)) (𝓝 ((-(n : ℂ)) • f n)) := by
  have hs := (ouGeneratorScalarError_tendsto n).sub (tendsto_const_nhds (x := (n : ℝ)))
  have hc := (Complex.continuous_ofReal.tendsto (-(n : ℝ))).comp (by simpa only [zero_sub] using hs)
  have hv := hc.smul (tendsto_const_nhds (x := f n))
  have ht : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have he : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      ((ouGeneratorScalarError n t - (n : ℝ) : ℝ) : ℂ) • f n = ouGeneratorQuotient H f t n := by
    filter_upwards [ht] with t ht
    change ((ouGeneratorScalarError n t - (n : ℝ) : ℝ) : ℂ) • f n =
      (t⁻¹ : ℂ) • (ouGeneratorDamping H t f n - f n)
    rw [ouGeneratorDamping_nonneg H t ht.le, degreeDamping_degree]
    simp only [ouGeneratorScalarError, degreeWeight]
    push_cast
    simp only [div_eq_mul_inv]
    module
  simpa only [Function.comp_def, Complex.ofReal_neg, Complex.ofReal_natCast] using hv.congr' he

/-- Any strong quotient limit has the genuine expected coefficient in every completed grade. -/
theorem ouGenerator_coordinates_of_tendsto (f z : TensorFullFock H)
    (h : Tendsto (ouGeneratorQuotient H f) (𝓝[>] (0 : ℝ)) (𝓝 z)) :
    ∀ n : ℕ, z n = (-(n : ℂ)) • f n := by
  intro n
  have hc := ((lp.evalCLM ℂ (fun m => TensorPower H m) 2 n).continuous.tendsto z).comp h
  change Tendsto (fun t => ouGeneratorQuotient H f t n) (𝓝[>] (0 : ℝ)) (𝓝 (z n)) at hc
  exact tendsto_nhds_unique hc (ouGeneratorQuotient_degree_tendsto H f n)

/-- Existence of a strong quotient limit forces membership in the EXACT weighted operator domain. -/
theorem ouGenerator_mem_domain_of_tendsto (f z : TensorFullFock H)
    (h : Tendsto (ouGeneratorQuotient H f) (𝓝[>] (0 : ℝ)) (𝓝 z)) :
    f ∈ numberOperatorDomain H := by
  change Memℓp (fun n : ℕ => (n : ℂ) • f n) 2
  convert lp.memℓp (-z) using 1
  funext n
  change (n : ℂ) • f n = -(z n)
  rw [ouGenerator_coordinates_of_tendsto H f z h n, neg_smul, neg_neg]

/-- Full exact right strong-generator graph, with no assumption outside the true domain. -/
theorem ouGenerator_graph_iff (f z : TensorFullFock H) :
    Tendsto (ouGeneratorQuotient H f) (𝓝[>] (0 : ℝ)) (𝓝 z) ↔
      ∃ g : numberOperatorDomain H, (g : TensorFullFock H) = f ∧ z = -numberOperator H g := by
  constructor
  · intro h
    refine ⟨⟨f, ouGenerator_mem_domain_of_tendsto H f z h⟩, rfl, ?_⟩
    apply lp.ext
    funext n
    change z n = -((n : ℂ) • f n)
    rw [ouGenerator_coordinates_of_tendsto H f z h n, neg_smul]
  · rintro ⟨g, rfl, rfl⟩
    exact ouGenerator_right_tendsto H g

 theorem ouGenerator_domain_iff (f : TensorFullFock H) :
    (∃ z : TensorFullFock H, Tendsto (ouGeneratorQuotient H f) (𝓝[>] (0 : ℝ)) (𝓝 z)) ↔
      f ∈ numberOperatorDomain H := by
  constructor
  · rintro ⟨z, hz⟩
    exact ouGenerator_mem_domain_of_tendsto H f z hz
  · intro hf
    exact ⟨-numberOperator H ⟨f, hf⟩, ouGenerator_right_tendsto H ⟨f, hf⟩⟩

end FreeProbability.Fock
