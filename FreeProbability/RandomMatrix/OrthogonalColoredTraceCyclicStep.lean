import FreeProbability.RandomMatrix.OrthogonalColoredTraceRightCenter

/-! # Actual selected-color reduction from shorter-run limits -/

noncomputable section
open scoped Classical Topology
namespace FreeProbability.Orthogonal
open Matrix MeasureTheory Filter ProbabilityTheory

/-- The actual whole except-color tuple is a measurable random variable. -/
theorem measurable_exceptHaarVariables {Ω Θ I n : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [Fintype n] [DecidableEq n] (Y : Ω → Θ) (X : I → Ω → Group n)
    (hY : Measurable Y) (hX : ∀ c, Measurable (X c)) (c : I) :
    Measurable (fun ω (j : {j : Unit ⊕ I // j ≠ Sum.inr c}) => augmentedHaarVariables Y X j.val ω) := by
  apply measurable_pi_iff.mpr
  rintro ⟨j, hj⟩
  cases j with
  | inl _ => exact MeasurableEquiv.ulift.symm.measurable.comp hY
  | inr d => exact MeasurableEquiv.ulift.symm.measurable.comp (hX d)

/-- CONDITIONAL selected-color reduction: actual shorter-run trace limits imply
actual colored trace convergence. The run limits are explicit inputs here;
the subsequent word-length induction must discharge them. -/
theorem ae_coloredTraceWord_tendsto_of_run_limits {Ω α I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (Θ : ℕ → Type*) [∀ N, MeasurableSpace (Θ N)]
    (color : α → I) (c : I) (word : List α) (hw : word ≠ []) (hfirst : color (word.head hw) = c)
    (K : ℝ) (hK : 0 ≤ K)
    (A : ∀ N : ℕ, Θ N → α → Matrix (Fin N) (Fin N) ℂ) (hAm : ∀ N, Measurable (A N))
    (Y : ∀ N : ℕ, Ω → Θ N) (X : ∀ N : ℕ, I → Ω → Group (Fin N))
    (hY : ∀ N, Measurable (Y N)) (hXm : ∀ N d, Measurable (X N d))
    (hX : ∀ N d, MeasurePreserving (X N d) μ (haar (Fin N)))
    (hi : ∀ N, iIndepFun (augmentedHaarVariables (Y N) (X N)) μ)
    (hA : ∀ N, ∀ᵐ ω ∂μ, ∀ a ∈ word, Matrix.trace (A N (Y N ω) a) = 0)
    (hAn : ∀ N, ∀ᵐ ω ∂μ, ∀ a ∈ word, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A N (Y N ω) a)‖ ≤ K)
    (hrun : ∀ᵐ ω ∂μ, ∀ k : Fin (selectedColorSegments color c word).length,
      Tendsto (fun N => normalizedTrace (selectedColorRunMatrix color c word (A N (Y N ω))
        (fun d => X N d ω) k)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, Tendsto (fun N => coloredTraceWord color word (A N (Y N ω)) (fun d => X N d ω))
      atTop (𝓝 0) := by
  let D := fun N : ℕ => ExceptHaarData (Θ N) I (Fin N) c
  let Z : ∀ N : ℕ, Ω → D N := fun N ω j => augmentedHaarVariables (Y N) (X N) j.val ω
  let P := fun N => selectedHeadDataMatrices color c word (A N)
  let Q := fun N z k => matrixTraceCenter (selectedRunDataMatrices color c word (A N) z k)
  let H : ℝ := K + 2 * (K + 1) ^ word.length
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hHK : K ≤ H := by
    dsimp only [H]
    have hp : 0 ≤ (K + 1) ^ word.length := by positivity
    linarith
  have hHB : (K + 1) ^ word.length ≤ H := by
    dsimp only [H]
    have hp : 0 ≤ (K + 1) ^ word.length := by positivity
    linarith
  have hP (N : ℕ) : Measurable (P N) := measurable_selectedHeadDataMatrices color c word (A N) (hAm N)
  have hQ (N : ℕ) : Measurable (Q N) := by
    apply measurable_pi_iff.mpr
    intro k
    exact measurable_matrixTraceCenter.comp (measurable_selectedRunDataMatrices color c word (A N) (hAm N)).eval
  have hZ (N : ℕ) : Measurable (Z N) := measurable_exceptHaarVariables (Y N) (X N) (hY N) (hXm N) c
  have hZi (N : ℕ) : IndepFun (Z N) (X N c) μ :=
    augmentedHaar_except_independent μ (Y N) (X N) (hY N) (hXm N) (hi N) c
  have hPc (N : ℕ) : ∀ᵐ ω ∂μ, ∀ k, Matrix.trace (P N (Z N ω) k) = 0 := by
    filter_upwards [hA N] with ω hω
    intro k
    exact hω _ (selectedColorHead_mem color c word k)
  have hQc (N : ℕ) : ∀ᵐ ω ∂μ, ∀ k, Matrix.trace (Q N (Z N ω) k) = 0 :=
    Eventually.of_forall (fun ω k => matrixTraceCenter_trace _)
  have hPn (N : ℕ) : ∀ᵐ ω ∂μ, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (P N (Z N ω) k)‖ ≤ H := by
    filter_upwards [hAn N] with ω hω
    intro k
    exact (hω _ (selectedColorHead_mem color c word k)).trans hHK
  have hQn (N : ℕ) : ∀ᵐ ω ∂μ, ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (Q N (Z N ω) k)‖ ≤ H := by
    filter_upwards [hAn N] with ω hω
    intro k
    have hb := selectedRunDataMatrices_opNorm_le color c word (A N) (Y N) (X N) ω K hK hω k
    exact ((matrixTraceCenter_opNorm_le _).trans (mul_le_mul_of_nonneg_left hb (by positivity))).trans
      (by dsimp only [H]; linarith)
  have hz := ae_variableData_traceWord_tendsto_of_source μ D
    (selectedColorSegments_length_pos color c word hw) H hH P Q hP hQ Z (fun N => X N c) hZ
    (fun N => hX N c) hZi hPc hQc hPn hQn
  filter_upwards [hz, hrun, ae_all_iff.mpr hAn] with ω hzω hrω hnω
  let AP := fun N k => A N (Y N ω) (selectedColorHead color c word k)
  let BP := fun N k => selectedColorRunMatrix color c word (A N (Y N ω)) (fun d => X N d ω) k
  have hAP : ∀ N k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (AP N k)‖ ≤ H := by
    intro N k
    exact (hnω N _ (selectedColorHead_mem color c word k)).trans hHK
  have hBP : ∀ N k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (BP N k)‖ ≤ H := by
    intro N k
    have hb := selectedRunDataMatrices_opNorm_le color c word (A N) (Y N) (X N) ω K hK (hnω N) k
    rw [selectedRunDataMatrices_apply] at hb
    exact hb.trans hHB
  have hc : Tendsto (fun N => traceWord (AP N) (fun k => matrixTraceCenter (BP N k)) (X N c ω))
      atTop (𝓝 0) := by
    simpa only [P, Q, Z, selectedHeadDataMatrices_apply, selectedRunDataMatrices_apply] using hzω
  have hd := tendsto_traceWord_right_center_sub H hH AP BP (fun N => X N c ω) hAP hBP hrω
  have ht : Tendsto (fun N => traceWord (AP N) (BP N) (X N c ω)) atTop (𝓝 0) := by
    simpa only [sub_add_cancel, add_zero] using hd.add hc
  have he : (fun N => coloredTraceWord color word (A N (Y N ω)) (fun d => X N d ω)) =
      (fun N => traceWord (AP N) (BP N) (X N c ω)) := by
    funext N
    exact coloredTraceWord_eq_selected color c word hw hfirst _ _
  rw [he]
  exact ht

end FreeProbability.Orthogonal
