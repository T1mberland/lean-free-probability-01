import FreeProbability.OperatorValued.PositiveOperatorMonotoneSupremum
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! # Actual order-supremum preservation from bounded WOT continuity -/
noncomputable section
open scoped Topology NNReal InnerProductSpace
open Filter
namespace FreeProbability
variable {J H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Genuine strong vector convergence implies actual weak operator convergence. -/
theorem operator_tendsto_WOT_of_strong {l : Filter J}
    (T : J → (H →L[ℂ] H)) (S : H →L[ℂ] H)
    (hlim : ∀ x, Tendsto (fun j => T j x) l (𝓝 (S x))) :
    Tendsto (fun j => ContinuousLinearMapWOT.ofCLM (T j)) l
      (𝓝 (ContinuousLinearMapWOT.ofCLM S)) := by
  apply ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr
  intro x y
  exact (tendsto_const_nhds : Tendsto (fun _ : J => y) l (𝓝 y)).inner (hlim x)

/-- A genuine monotone contraction continuous on every WOT norm ball preserves all bounded directed operator suprema. -/
theorem operator_isLUB_map_of_boundedWOT_continuous [Preorder J] [NeBot (atTop : Filter J)]
    (P : (H →L[ℂ] H) → (K →L[ℂ] K)) (hP : Monotone P)
    (hPn : ∀ A, ‖P A‖ ≤ ‖A‖)
    (hPc : ∀ C : ℝ≥0, Continuous (fun A : {A : H →WOT[ℂ] H // ‖A.toCLM‖ ≤ C} =>
      ContinuousLinearMapWOT.ofCLM (P A.val.toCLM)))
    (T : J → (H →L[ℂ] H)) (hT : Monotone T) (C : ℝ≥0) (hn : ∀ j, ‖T j‖ ≤ C)
    (S : H →L[ℂ] H) (hS : IsLUB (Set.range T) S) :
    IsLUB (Set.range (fun j => P (T j))) (P S) := by
  obtain ⟨R, hR, hlim, hRn⟩ := monotoneOperator_exists_isLUB T hT C hn
  have he : R = S := hR.unique hS
  subst R
  let u : J → {A : H →WOT[ℂ] H // ‖A.toCLM‖ ≤ C} := fun j =>
    ⟨ContinuousLinearMapWOT.ofCLM (T j), hn j⟩
  let v : {A : H →WOT[ℂ] H // ‖A.toCLM‖ ≤ C} :=
    ⟨ContinuousLinearMapWOT.ofCLM S, hRn⟩
  have hu : Tendsto u atTop (𝓝 v) :=
    tendsto_subtype_rng.mpr (operator_tendsto_WOT_of_strong T S hlim)
  have hpw : Tendsto (fun j => ContinuousLinearMapWOT.ofCLM (P (T j))) atTop
      (𝓝 (ContinuousLinearMapWOT.ofCLM (P S))) :=
    ((hPc C).tendsto v).comp hu
  have hPT : Monotone (fun j => P (T j)) := hP.comp hT
  have hPTn (j : J) : ‖P (T j)‖ ≤ C := (hPn _).trans (hn j)
  obtain ⟨Q, hQ, hQlim, _⟩ := monotoneOperator_exists_isLUB (fun j => P (T j)) hPT C hPTn
  have hqe : Q = P S := ContinuousLinearMapWOT.ofCLM_injective
    (tendsto_nhds_unique (operator_tendsto_WOT_of_strong _ Q hQlim) hpw)
  rwa [hqe] at hQ
/-- Normality in the positive directed-supremum sense, with no separate norm-bound hypothesis. -/
theorem operator_isLUB_map_of_boundedWOT_continuous_of_nonneg
    [Preorder J] [NeBot (atTop : Filter J)]
    (P : (H →L[ℂ] H) → (K →L[ℂ] K)) (hP : Monotone P)
    (hPn : ∀ A, ‖P A‖ ≤ ‖A‖)
    (hPc : ∀ C : ℝ≥0, Continuous (fun A : {A : H →WOT[ℂ] H // ‖A.toCLM‖ ≤ C} =>
      ContinuousLinearMapWOT.ofCLM (P A.val.toCLM)))
    (T : J → (H →L[ℂ] H)) (hT : Monotone T) (hp : ∀ j, 0 ≤ T j)
    (S : H →L[ℂ] H) (hS : IsLUB (Set.range T) S) :
    IsLUB (Set.range (fun j => P (T j))) (P S) := by
  apply operator_isLUB_map_of_boundedWOT_continuous P hP hPn hPc T hT ‖S‖₊ _ S hS
  intro j
  exact CStarAlgebra.norm_le_norm_of_le_of_nonneg (hS.1 ⟨j, rfl⟩) (hp j)
end FreeProbability
