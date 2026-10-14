import FreeProbability.Fock.FullFock

/-!
# Explicit recursively completed tensor powers and their full Fock unitary

`TensorPower H (n+1)` is literally `Completion (H ⊗ TensorPower H n)`.
The zeroth power uses the complete scalar level, with its explicit scalar unitary,
so all levels live in the universe of `H`. Their Hilbert sum is explicitly
unitarily identified with `FullFock H`; creation is literal tensoring.
-/

noncomputable section
open scoped Classical InnerProductSpace TensorProduct ENNReal
open UniformSpace

namespace FreeProbability.Fock

universe u

/-- A complete Hilbert space bundled only to make recursive tensor instances explicit. -/
structure CompleteHilbertLevel where
  Carrier : Type u
  [normed : NormedAddCommGroup Carrier]
  [inner : InnerProductSpace ℂ Carrier]
  [complete : CompleteSpace Carrier]

attribute [instance] CompleteHilbertLevel.normed CompleteHilbertLevel.inner CompleteHilbertLevel.complete

variable (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Literal recursively completed Hilbert tensor powers. The zero level is explicitly scalar. -/
def tensorPowerBundle : ℕ → CompleteHilbertLevel.{u}
  | 0 => { Carrier := FullFockLevel H 0 }
  | n + 1 => { Carrier := Completion (H ⊗[ℂ] (tensorPowerBundle n).Carrier) }

/-- The type underlying a genuine recursive completed Hilbert tensor power. -/
abbrev TensorPower (n : ℕ) := (tensorPowerBundle H n).Carrier

/-- Exact scalar unitary for the zeroth recursive tensor power. -/
def tensorPowerZero : ℂ ≃ₗᵢ[ℂ] TensorPower H 0 := fullFockScalarLevel H

/-- Explicit identification of the recursive tensor powers with complete word levels. -/
def tensorPowerLevelEquiv : ∀ n, TensorPower H n ≃ₗᵢ[ℂ] FullFockLevel H n
  | 0 => LinearIsometryEquiv.refl ℂ _
  | n + 1 =>
    (isometryEquivCompletion (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ H)
      (tensorPowerLevelEquiv n))).trans (fullFockTensorLevel H n)

section HilbertSumTransport

variable {K : Type*} {E F : K → Type*} [∀ k, NormedAddCommGroup (E k)]
  [∀ k, NormedSpace ℂ (E k)] [∀ k, NormedAddCommGroup (F k)] [∀ k, NormedSpace ℂ (F k)]

/-- Coordinate transport by actual unitary maps preserves genuine Hilbert summability. -/
def hilbertSumMap (e : ∀ k, E k ≃ₗᵢ[ℂ] F k) (f : lp E 2) : lp F 2 :=
  ⟨fun k => e k (f k), by
    apply Memℓp.of_norm
    simpa only [(e _).norm_map] using (lp.memℓp f).norm⟩

@[simp] theorem hilbertSumMap_apply (e : ∀ k, E k ≃ₗᵢ[ℂ] F k) (f : lp E 2) (k : K) :
    hilbertSumMap e f k = e k (f k) := rfl

/-- Unitary coordinate transport of an entire infinite Hilbert direct sum. -/
def hilbertSumEquiv (e : ∀ k, E k ≃ₗᵢ[ℂ] F k) : lp E 2 ≃ₗᵢ[ℂ] lp F 2 where
  toFun := hilbertSumMap e
  invFun := hilbertSumMap (fun k => (e k).symm)
  left_inv f := by ext k; simp
  right_inv f := by ext k; simp
  map_add' f g := by ext k; simp
  map_smul' c f := by ext k; simp
  norm_map' f := by
    change ‖hilbertSumMap e f‖ = ‖f‖
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal),
      lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    congr 1
    congr 1
    funext k
    exact congrArg (fun r : ℝ => r ^ (2 : ℝ≥0∞).toReal) ((e k).norm_map (f k))

@[simp] theorem hilbertSumEquiv_single [DecidableEq K] (e : ∀ k, E k ≃ₗᵢ[ℂ] F k) (k : K) (f : E k) :
    hilbertSumEquiv e (lp.single 2 k f) = lp.single 2 k (e k f) := by
  ext j
  by_cases h : j = k
  · subst j; simp [hilbertSumEquiv, hilbertSumMap, lp.single_apply]
  · simp [hilbertSumEquiv, hilbertSumMap, lp.single_apply, h]

end HilbertSumTransport

/-- The actual infinite Hilbert sum of recursively completed tensor powers. -/
abbrev TensorFullFock := lp (fun n => TensorPower H n) 2

/-- Explicit unitary from word Fock space onto the full sum of genuine completed tensors. -/
def fullFockTensorDecomposition : FullFock H ≃ₗᵢ[ℂ] TensorFullFock H :=
  (fullFockGrading H).trans (hilbertSumEquiv (tensorPowerLevelEquiv H)).symm

/-- The canonical isometric inclusion of each genuine tensor power into full Fock space. -/
def tensorPowerEmbedding (n : ℕ) : TensorPower H n →ₗᵢ[ℂ] FullFock H :=
  (levelEmbedding n).comp (tensorPowerLevelEquiv H n).toLinearIsometry

/-- The explicit direct-sum unitary carries pure tensors to their canonical Fock inclusions. -/
@[simp] theorem fullFockTensorDecomposition_symm_single (n : ℕ) (f : TensorPower H n) :
    (fullFockTensorDecomposition H).symm (lp.single 2 n f) = tensorPowerEmbedding H n f := by
  change (fullFockGrading H).symm
    (hilbertSumEquiv (tensorPowerLevelEquiv H) (lp.single 2 n f)) = _
  have hl : (fullFockGrading H).symm (lp.single 2 n (tensorPowerLevelEquiv H n f)) =
      tensorPowerEmbedding H n f := by
    convert lengthDecomposition_symm_single n (tensorPowerLevelEquiv H n f) using 1 <;> rfl
  exact (congrArg (fullFockGrading H).symm
    (hilbertSumEquiv_single (tensorPowerLevelEquiv H) n f)).trans hl

/-- Scalar tensors occupy exactly the vacuum sector. -/
@[simp] theorem tensorPowerEmbedding_zero (c : ℂ) :
    tensorPowerEmbedding H 0 (tensorPowerZero H c) = c • fullVacuum H := by
  change levelEmbedding 0 (scalarLevelIsometry c) = _
  simp [scalarLevelIsometry, LinearIsometry.toSpanSingleton_apply, levelEmbedding_single,
    emptyTuple, fullVacuum, vacuum]

/-- The direct-sum vacuum is exactly the scalar unit in tensor degree zero. -/
@[simp] theorem fullFockTensorDecomposition_vacuum :
    fullFockTensorDecomposition H (fullVacuum H) = lp.single 2 0 (tensorPowerZero H 1) := by
  apply (fullFockTensorDecomposition H).symm.injective
  simp

/-- Creation literally tensors on the explicit recursive powers, not only their word models. -/
theorem tensorPowerEmbedding_creation (n : ℕ) (h : H) (f : TensorPower H n) :
    tensorPowerEmbedding H (n + 1)
      ((h ⊗ₜ[ℂ] f : H ⊗[ℂ] TensorPower H n) : Completion (H ⊗[ℂ] TensorPower H n)) =
      fullCreation H h (tensorPowerEmbedding H n f) := by
  change levelEmbedding (n + 1) (fullFockTensorLevel H n
    (isometryEquivCompletion _ _)) = _
  rw [isometryEquivCompletion_coe]
  simp only [TensorProduct.congrIsometry_apply, TensorProduct.congr_tmul]
  exact fullCreation_tensorLevel H n h (tensorPowerLevelEquiv H n f)

end FreeProbability.Fock
