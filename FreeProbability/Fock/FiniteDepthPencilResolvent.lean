import FreeProbability.Fock.FiniteDepthRetainedPowers
import FreeProbability.OperatorValued.SpectralShiftNorm
import FreeProbability.OperatorValued.OperatorScaledResolventComparison

/-! # Quantitative actual finite-depth exterior pencil resolvents

We compress the positive shifted pencil. This retains the full right-exterior
domain even when the upper spectral edge and the spectral parameter are negative.
-/
noncomputable section
open scoped Classical Ring ENNReal
namespace FreeProbability.Fock
variable {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n] [Nonempty n]

local instance : PartialOrder (HilbertMatrixSpace n (WordSpace I) →L[ℂ]
    HilbertMatrixSpace n (WordSpace I)) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (HilbertMatrixSpace n (WordSpace I) →L[ℂ]
    HilbertMatrixSpace n (WordSpace I)) := CStarAlgebra.spectralOrderedRing _
local instance : Nontrivial (HilbertMatrixSpace n (WordSpace I) →L[ℂ]
    HilbertMatrixSpace n (WordSpace I)) := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro h
  let j : n := Classical.choice inferInstance
  let x : HilbertMatrixSpace n (WordSpace I) := lp.single 2 j vacuum
  have hh := congrArg (fun T : HilbertMatrixSpace n (WordSpace I) →L[ℂ]
    HilbertMatrixSpace n (WordSpace I) => ‖T x‖) h
  simp [x, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)] at hh

omit [Nonempty n] in
theorem finiteDepthPencilOperator_isSelfAdjoint (C₀ : Matrix n n ℂ)
    (C : I → Matrix n n ℂ) (hC₀ : C₀.IsHermitian) (hC : ∀ i, (C i).IsHermitian) :
    IsSelfAdjoint (finiteDepthPencilOperator C₀ C) :=
  (operatorMatrixPencil_isSelfAdjoint C₀ C hC₀ hC).map
    (hilbertMatrixStarAlgEquiv (N := n) (E := WordSpace I))

/-- The genuine upper edge of the bounded pencil on its complete matrix Fock space. -/
def finiteDepthPencilUpperEdge (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ) : ℝ :=
  realSpectralMaximum (finiteDepthPencilOperator C₀ C)

theorem finiteDepthPencilUpperEdge_add_norm_nonneg (C₀ : Matrix n n ℂ)
    (C : I → Matrix n n ℂ) (hC₀ : C₀.IsHermitian) (hC : ∀ i, (C i).IsHermitian) :
    0 ≤ finiteDepthPencilUpperEdge C₀ C + ‖finiteDepthPencilOperator C₀ C‖ :=
  realSpectralMaximum_add_norm_nonneg _ (finiteDepthPencilOperator_isSelfAdjoint C₀ C hC₀ hC)

/-- Ambient inverse of the compressed positive shift. On the retained range this is the usual truncated pencil resolvent. -/
def finiteDepthPencilResolvent (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ)
    (L : ℕ) (z : ℝ) : HilbertMatrixSpace n (WordSpace I) →L[ℂ]
      HilbertMatrixSpace n (WordSpace I) :=
  (((z + ‖finiteDepthPencilOperator C₀ C‖ : ℝ) : ℂ) • 1 -
    matrixDepthProjection L *
      (finiteDepthPencilOperator C₀ C + (‖finiteDepthPencilOperator C₀ C‖ : ℂ) • 1) *
    matrixDepthProjection L)⁻¹ʳ

/-- Every real point above the actual upper edge has an explicit geometric finite-depth error on all vacuum-level vectors. -/
theorem finiteDepthPencilResolvent_error (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ)
    (hC₀ : C₀.IsHermitian) (hC : ∀ i, (C i).IsHermitian) (L : ℕ) (z : ℝ)
    (hz : finiteDepthPencilUpperEdge C₀ C < z)
    {x : HilbertMatrixSpace n (WordSpace I)} (hx : x ∈ matrixDepthSpace 0) :
    ‖((z : ℂ) • 1 - finiteDepthPencilOperator C₀ C)⁻¹ʳ x -
        finiteDepthPencilResolvent C₀ C L z x‖ ≤
      2 * ((finiteDepthPencilUpperEdge C₀ C + ‖finiteDepthPencilOperator C₀ C‖) /
        (z + ‖finiteDepthPencilOperator C₀ C‖)) ^ (L + 1) /
        (z - finiteDepthPencilUpperEdge C₀ C) * ‖x‖ := by
  let H := finiteDepthPencilOperator C₀ C
  have hH : IsSelfAdjoint H := finiteDepthPencilOperator_isSelfAdjoint C₀ C hC₀ hC
  have hR := realSpectralMaximum_add_norm_nonneg H hH
  have hn : ‖H + (‖H‖ : ℂ) • 1‖ ≤ realSpectralMaximum H + ‖H‖ := by
    simpa only [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul] using
      norm_positiveSpectralShift_le H hH
  have hp : ∀ k ≤ L, matrixDepthProjection L
      (((H + (‖H‖ : ℂ) • 1) ^ k) x) = ((H + (‖H‖ : ℂ) • 1) ^ k) x := by
    intro k hk
    apply (matrixDepthProjection_eq_self_iff L _).mpr
    exact matrixDepthSpace_mono hk (shiftedPencil_pow_mem_depth C₀ C (‖H‖ : ℂ) hx k)
  have hh := scaledInverse_sandwich_comparison (matrixDepthProjection L)
    (H + (‖H‖ : ℂ) • 1) (realSpectralMaximum H + ‖H‖) (z + ‖H‖)
    hR (by dsimp [finiteDepthPencilUpperEdge] at hz; linarith) hn
    (norm_matrixDepthProjection_le L) L x hp
  have he : ((z + ‖H‖ : ℝ) : ℂ) • (1 : HilbertMatrixSpace n (WordSpace I) →L[ℂ]
      HilbertMatrixSpace n (WordSpace I)) - (H + (‖H‖ : ℂ) • 1) = (z : ℂ) • 1 - H := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [smul_apply, sub_apply, add_apply, Complex.ofReal_add, _root_.add_smul]
    abel
  rw [he] at hh
  simpa only [finiteDepthPencilResolvent, finiteDepthPencilUpperEdge, H,
    add_sub_add_right_eq_sub] using hh

end FreeProbability.Fock
