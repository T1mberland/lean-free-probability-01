import FreeProbability.OperatorValued.PositiveOperatorMonotoneCoefficients
import Mathlib.Topology.MetricSpace.Cauchy

/-! # Genuine vector Cauchy limits of bounded monotone directed operator nets -/
noncomputable section
open scoped InnerProductSpace Topology
open Filter
namespace FreeProbability
variable {J H : Type*} [Preorder J] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H] [NeBot (atTop : Filter J)]

/-- Every vector orbit of an arbitrary norm-bounded Loewner-monotone directed net is Cauchy. -/
theorem monotoneOperator_vector_cauchy (T : J → (H →L[ℂ] H)) (hT : Monotone T)
    (M : ℝ) (hM : ∀ j, ‖T j‖ ≤ M) (x : H) :
    Cauchy (Filter.map (fun j => T j x) atTop) := by
  have hd := Filter.atTop_neBot_iff.mp (inferInstance : NeBot (atTop : Filter J))
  let : Nonempty J := hd.1
  let : IsDirectedOrder J := hd.2
  have hM0 : 0 ≤ M := (norm_nonneg (T (Classical.arbitrary J))).trans (hM _)
  let q : J → ℝ := fun j => (inner ℂ x (T j x)).re
  let L : ℝ := ⨆ j, q j
  have hb : BddAbove (Set.range q) := positiveOperatorQuadratic_bddAbove T M hM x
  have hq : Tendsto q atTop (𝓝 L) := positiveOperatorQuadratic_tendsto T hT M hM x
  have hl (j : J) : q j ≤ L := le_ciSup hb j
  apply Metric.cauchy_iff.mpr
  refine ⟨inferInstance, ?_⟩
  intro ε hε
  let δ : ℝ := (ε / 2) ^ 2 / (2 * M + 1)
  have hden : 0 < 2 * M + 1 := by positivity
  have hδ : 0 < δ := div_pos (sq_pos_of_pos (half_pos hε)) hden
  have hmδ : (2 * M + 1) * δ = (ε / 2) ^ 2 := by
    exact mul_div_cancel₀ _ (ne_of_gt hden)
  have hsmall : 2 * M * δ < (ε / 2) ^ 2 := by nlinarith
  have hzero : Tendsto (fun j => L - q j) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : J => L) atTop (𝓝 L)).sub hq)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hzero.eventually (gt_mem_nhds hδ))
  have hclose {i j : J} (hi : N ≤ i) (hij : i ≤ j) : ‖T j x - T i x‖ < ε / 2 := by
    have he := positiveOperator_increment_energy_le T hT M hM x hij
    have hgap : q j - q i ≤ L - q i := sub_le_sub_right (hl j) _
    have hh := he.trans (mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ 2 * M))
    have ht := hN i hi
    have hbound : ‖T j x - T i x‖ ^ 2 < (ε / 2) ^ 2 :=
      (hh.trans (mul_le_mul_of_nonneg_left ht.le (by positivity : 0 ≤ 2 * M))).trans_lt hsmall
    nlinarith [norm_nonneg (T j x - T i x)]
  refine ⟨(fun j => T j x) '' Set.Ici N, image_mem_map (eventually_ge_atTop N), ?_⟩
  rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have hki : dist (T i x) (T k x) < ε / 2 := by
    rw [dist_comm, dist_eq_norm]
    exact hclose hi hik
  have hkj : dist (T j x) (T k x) < ε / 2 := by
    rw [dist_comm, dist_eq_norm]
    exact hclose hj hjk
  exact (dist_triangle_right _ _ _).trans_lt (by linarith)

/-- Completeness gives a genuine strong pointwise limit for every vector. -/
theorem monotoneOperator_vector_tendsto (T : J → (H →L[ℂ] H)) (hT : Monotone T)
    (M : ℝ) (hM : ∀ j, ‖T j‖ ≤ M) (x : H) :
    ∃ y : H, Tendsto (fun j => T j x) atTop (𝓝 y) :=
  cauchy_map_iff_exists_tendsto.mp (monotoneOperator_vector_cauchy T hT M hM x)
end FreeProbability
