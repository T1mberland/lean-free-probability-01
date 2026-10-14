import FreeProbability.RandomMatrix.OrthogonalColoredTraceEndpoints

/-! # Actual almost sure centered colored trace criterion -/

noncomputable section
open scoped Classical Topology
namespace FreeProbability.Orthogonal
open Matrix MeasureTheory Filter ProbabilityTheory
universe u

/-- Actual centered alternating trace convergence for a finite jointly
independent family of Haar orthogonal matrices and an entire independent
random input data coordinate. There are no shorter-word limit premises. -/
theorem ae_coloredTraceWord_tendsto {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (Θ : ℕ → Type*) [∀ N, MeasurableSpace (Θ N)]
    {α : Type u} (color : α → I) (word : List α) (hw : word ≠ [])
    (halt : word.IsChain (fun a b => color a ≠ color b)) (K : ℝ) (hK : 0 ≤ K)
    (A : ∀ N : ℕ, Θ N → α → Matrix (Fin N) (Fin N) ℂ) (hAm : ∀ N, Measurable (A N))
    (Y : ∀ N : ℕ, Ω → Θ N) (X : ∀ N : ℕ, I → Ω → Group (Fin N))
    (hY : ∀ N, Measurable (Y N)) (hXm : ∀ N d, Measurable (X N d))
    (hX : ∀ N d, MeasurePreserving (X N d) μ (haar (Fin N)))
    (hi : ∀ N, iIndepFun (augmentedHaarVariables (Y N) (X N)) μ)
    (hA : ∀ N, ∀ᵐ ω ∂μ, ∀ a ∈ word, Matrix.trace (A N (Y N ω) a) = 0)
    (hAn : ∀ N, ∀ᵐ ω ∂μ, ∀ a ∈ word, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A N (Y N ω) a)‖ ≤ K) :
    ∀ᵐ ω ∂μ, Tendsto (fun N => coloredTraceWord color word (A N (Y N ω)) (fun d => X N d ω))
      atTop (𝓝 0) := by
  generalize hlen : word.length = m
  induction m using Nat.strong_induction_on generalizing α word color K with
  | h m ih =>
    cases word with
    | nil => exact False.elim (hw rfl)
    | cons a tail =>
      cases tail with
      | nil =>
        have he (N : ℕ) : ∀ᵐ ω ∂μ, coloredTraceWord color [a] (A N (Y N ω)) (fun d => X N d ω) = 0 := by
          filter_upwards [hA N] with ω hω
          simp only [coloredTraceWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
            coloredConjugateBlock]
          rw [normalizedTrace_orthogonal_conjugate, normalizedTrace, hω a (by simp), mul_zero]
        filter_upwards [ae_all_iff.mpr he] with ω hω
        have hf : (fun N => coloredTraceWord color [a] (A N (Y N ω)) (fun d => X N d ω)) = fun _ => 0 :=
          funext (fun N => hω N)
        rw [hf]
        exact tendsto_const_nhds
      | cons d tail =>
        obtain ⟨middle, b, he⟩ : ∃ (middle : List α) (b : α), d :: tail = middle ++ [b] :=
          ⟨(d :: tail).dropLast, (d :: tail).getLast (by simp), (List.dropLast_append_getLast (by simp)).symm⟩
        rw [he] at hw halt hA hAn hlen ⊢
        simp only [List.length_cons, List.length_append, List.length_nil] at hlen
        by_cases hsame : color a = color b
        · have hmid : middle ≠ [] := endpointInterior_ne_nil color a b middle hsame halt
          have hmidalt : middle.IsChain (fun a b => color a ≠ color b) :=
            halt.tail.left_of_append
          have hmidA (N : ℕ) : ∀ᵐ ω ∂μ, ∀ x ∈ middle, Matrix.trace (A N (Y N ω) x) = 0 := by
            filter_upwards [hA N] with ω hω
            intro x hx
            exact hω x (by simp [hx])
          have hmidAn (N : ℕ) : ∀ᵐ ω ∂μ, ∀ x ∈ middle,
              ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A N (Y N ω) x)‖ ≤ K := by
            filter_upwards [hAn N] with ω hω
            intro x hx
            exact hω x (by simp [hx])
          have hI : ∀ᵐ ω ∂μ, Tendsto (fun N => coloredTraceWord color middle (A N (Y N ω))
              (fun d => X N d ω)) atTop (𝓝 0) := by
            apply ih middle.length (by omega)
              color middle hmid hmidalt K hK A hAm
            · exact hmidA
            · exact hmidAn
            · rfl
          let M := fun N θ => endpointCoefficients (A N θ) a b
          let KM := K + 2 * K ^ 2
          have hKM : 0 ≤ KM := by dsimp only [KM]; positivity
          have hMm (N : ℕ) : Measurable (M N) := measurable_endpointCoefficients (A N) (hAm N) a b
          have hMc (N : ℕ) : ∀ᵐ ω ∂μ, ∀ x ∈ endpointWord middle, Matrix.trace (M N (Y N ω) x) = 0 := by
            filter_upwards [hmidA N] with ω hω
            exact endpointCoefficients_trace _ a b middle hω
          have hMn (N : ℕ) : ∀ᵐ ω ∂μ, ∀ x ∈ endpointWord middle,
              ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (M N (Y N ω) x)‖ ≤ KM := by
            filter_upwards [hAn N] with ω hω
            exact endpointCoefficients_opNorm_le _ a b middle K hK (hω a (by simp))
              (hω b (by simp)) (fun x hx => hω x (by simp [hx]))
          have hM : ∀ᵐ ω ∂μ, Tendsto (fun N => coloredTraceWord (endpointColor color (color a))
              (endpointWord middle) (M N (Y N ω)) (fun d => X N d ω)) atTop (𝓝 0) := by
            apply ih (endpointWord middle).length (by simp only [endpointWord, List.length_cons, List.length_map]; omega)
              (endpointColor color (color a)) (endpointWord middle) (by simp [endpointWord])
              (endpointWord_alternating color (color a) a b middle rfl halt) KM hKM M hMm
            · exact hMc
            · exact hMn
            · rfl
          filter_upwards [hI, hM, ae_all_iff.mpr hAn] with ω hIω hMω hnω
          have hs : Tendsto (fun N => normalizedTrace (A N (Y N ω) b * A N (Y N ω) a) *
              coloredTraceWord color middle (A N (Y N ω)) (fun d => X N d ω)) atTop (𝓝 0) := by
            apply squeeze_zero_norm' (a := fun N => K ^ 2 *
              ‖coloredTraceWord color middle (A N (Y N ω)) (fun d => X N d ω)‖)
            · filter_upwards with N
              rw [norm_mul]
              have hp : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A N (Y N ω) b * A N (Y N ω) a)‖ ≤ K ^ 2 := by
                rw [map_mul]
                have hbN := hnω N b (by simp)
                have haN := hnω N a (by simp)
                have hm := mul_le_mul hbN haN (norm_nonneg _) hK
                exact (norm_mul_le _ _).trans (by simpa only [pow_two] using hm)
              exact mul_le_mul_of_nonneg_right ((normalizedTrace_norm_le_Euclidean_opNorm _).trans hp) (norm_nonneg _)
            · have ht := tendsto_zero_iff_norm_tendsto_zero.mp hIω
              simpa only [mul_zero] using tendsto_const_nhds.mul (f := fun _ : ℕ => K ^ 2) ht
          have hew : (fun N => coloredTraceWord color (a :: middle ++ [b]) (A N (Y N ω)) (fun d => X N d ω)) =
              (fun N => coloredTraceWord (endpointColor color (color a)) (endpointWord middle) (M N (Y N ω))
                (fun d => X N d ω) + normalizedTrace (A N (Y N ω) b * A N (Y N ω) a) *
                  coloredTraceWord color middle (A N (Y N ω)) (fun d => X N d ω)) := by
            funext N
            exact coloredTraceWord_endpoint_decomposition color (color a) a b middle rfl hsame.symm _ _
          have ht := hMω.add hs
          simp only [add_zero] at ht
          exact ht.congr' (Eventually.of_forall (fun N => (congrFun hew N).symm))
        · have hw' : a :: middle ++ [b] ≠ [] := by simp
          have hlast : color ((a :: middle ++ [b]).getLast hw') ≠ color a := by
            have he : (a :: middle ++ [b]).getLast hw' = b := by
              simp
            rw [he]
            exact Ne.symm hsame
          apply ae_coloredTraceWord_tendsto_of_run_limits μ Θ color (color a) (a :: middle ++ [b]) hw' rfl
            K hK A hAm Y X hY hXm hX hi hA hAn
          apply ae_all_iff.mpr
          intro k
          let run := selectedColorRun color (color a) (a :: middle ++ [b]) k
          have hrun : run ≠ [] := selectedColorRun_ne_nil color (color a) _ hw' rfl hlast halt k
          have hrunalt := selectedColorRun_alternating color (color a) (a :: middle ++ [b]) halt k
          have hrunA (N : ℕ) : ∀ᵐ ω ∂μ, ∀ x ∈ run, Matrix.trace (A N (Y N ω) x) = 0 := by
            filter_upwards [hA N] with ω hω
            intro x hx
            exact hω x ((selectedColorRun_sublist color (color a) _ k).subset hx)
          have hrunAn (N : ℕ) : ∀ᵐ ω ∂μ, ∀ x ∈ run,
              ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A N (Y N ω) x)‖ ≤ K := by
            filter_upwards [hAn N] with ω hω
            intro x hx
            exact hω x ((selectedColorRun_sublist color (color a) _ k).subset hx)
          change ∀ᵐ ω ∂μ, Tendsto (fun N => coloredTraceWord color run (A N (Y N ω))
            (fun d => X N d ω)) atTop (𝓝 0)
          apply ih run.length (by
            change (selectedColorRun color (color a) (a :: middle ++ [b]) k).length < m
            have hl := selectedColorRun_length_lt color (color a) (a :: middle ++ [b]) k
            simp only [List.length_cons, List.length_append, List.length_nil] at hl
            omega)
            color run hrun hrunalt K hK A hAm
          · exact hrunA
          · exact hrunAn
          · rfl

end FreeProbability.Orthogonal
