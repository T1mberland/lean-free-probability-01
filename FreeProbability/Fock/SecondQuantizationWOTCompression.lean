import FreeProbability.Fock.SecondQuantizationCompressionCP
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology

/-!
# WOT continuity of actual ambient Fock compression and unitary conjugation

These are concrete coefficient-topology results for ambient bounded operators.
They do not assert a normal extension of the native generated-algebra embedding
or of the native OU self-map.
-/
noncomputable section
open scoped InnerProductSpace
namespace FreeProbability.Fock
section General
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Actual bounded-operator sandwich, with the genuine weak operator topology on both sides. -/
def boundedCompressionWOT (W : E →L[ℂ] F) (T : F →WOT[ℂ] F) : E →WOT[ℂ] E :=
  ContinuousLinearMapWOT.ofCLM (W.adjoint.comp (T.toCLM.comp W))

/-- Every coefficient of actual compression is a pulled-back ambient coefficient. -/
theorem boundedCompressionWOT_coefficient (W : E →L[ℂ] F) (T : F →WOT[ℂ] F) (x y : E) :
    inner ℂ y (boundedCompressionWOT W T x) = inner ℂ (W y) (T (W x)) :=
  W.adjoint_inner_right y (T (W x))

/-- Actual compression is continuous for WOT, for all bounded W and all ambient operator inputs. -/
theorem boundedCompressionWOT_continuous (W : E →L[ℂ] F) : Continuous (boundedCompressionWOT W) := by
  apply ContinuousLinearMapWOT.continuous_iff.mpr
  intro x y
  have heq : (fun T : F →WOT[ℂ] F => inner ℂ y (boundedCompressionWOT W T x)) =
      (fun T : F →WOT[ℂ] F => inner ℂ (W y) (T (W x))) :=
    funext (fun T => boundedCompressionWOT_coefficient W T x y)
  rw [heq]
  fun_prop

/-- Actual Hilbert-unitary bounded-operator conjugation, with WOT on domain and codomain. -/
def unitaryConjugationWOT (U : E ≃ₗᵢ[ℂ] F) (T : E →WOT[ℂ] E) : F →WOT[ℂ] F :=
  ContinuousLinearMapWOT.ofCLM (U.conjStarAlgEquiv T.toCLM)

/-- Conjugation pulls every WOT coefficient back through the actual inverse unitary. -/
theorem unitaryConjugationWOT_coefficient (U : E ≃ₗᵢ[ℂ] F) (T : E →WOT[ℂ] E) (x y : F) :
    inner ℂ y (unitaryConjugationWOT U T x) = inner ℂ (U.symm y) (T (U.symm x)) := by
  change inner ℂ y (U (T (U.symm x))) = _
  calc
    _ = inner ℂ (U (U.symm y)) (U (T (U.symm x))) := by rw [U.apply_symm_apply]
    _ = _ := U.inner_map_map _ _

/-- Genuine ambient unitary conjugation is WOT continuous. -/
theorem unitaryConjugationWOT_continuous (U : E ≃ₗᵢ[ℂ] F) : Continuous (unitaryConjugationWOT U) := by
  apply ContinuousLinearMapWOT.continuous_iff.mpr
  intro x y
  have heq : (fun T : E →WOT[ℂ] E => inner ℂ y (unitaryConjugationWOT U T x)) =
      (fun T : E →WOT[ℂ] E => inner ℂ (U.symm y) (T (U.symm x))) :=
    funext (fun T => unitaryConjugationWOT_coefficient U T x y)
  rw [heq]
  fun_prop
end General

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Actual second-quantized isometry compression in WOT. -/
def secondQuantizationCompressionWOT (V : H →ₗᵢ[ℂ] K) :
    (TensorFullFock K →WOT[ℂ] TensorFullFock K) → (TensorFullFock H →WOT[ℂ] TensorFullFock H) :=
  boundedCompressionWOT (secondQuantizationIsometry V).toContinuousLinearMap

/-- The WOT map is precisely the already verified actual compression, not an alternate model. -/
@[simp] theorem secondQuantizationCompressionWOT_toCLM (V : H →ₗᵢ[ℂ] K)
    (T : TensorFullFock K →WOT[ℂ] TensorFullFock K) :
    (secondQuantizationCompressionWOT V T).toCLM = secondQuantizationCompression V T.toCLM := rfl

theorem secondQuantizationCompressionWOT_continuous (V : H →ₗᵢ[ℂ] K) :
    Continuous (secondQuantizationCompressionWOT V) := boundedCompressionWOT_continuous _

/-- Actual second-quantized unitary conjugation in the ambient weak operator topology. -/
def secondQuantizationConjugationWOT (U : H ≃ₗᵢ[ℂ] H) :
    (TensorFullFock H →WOT[ℂ] TensorFullFock H) → (TensorFullFock H →WOT[ℂ] TensorFullFock H) :=
  unitaryConjugationWOT (secondQuantization U)

@[simp] theorem secondQuantizationConjugationWOT_toCLM (U : H ≃ₗᵢ[ℂ] H)
    (T : TensorFullFock H →WOT[ℂ] TensorFullFock H) :
    (secondQuantizationConjugationWOT U T).toCLM = (secondQuantization U).conjStarAlgEquiv T.toCLM := rfl

theorem secondQuantizationConjugationWOT_continuous (U : H ≃ₗᵢ[ℂ] H) :
    Continuous (secondQuantizationConjugationWOT U) := unitaryConjugationWOT_continuous _

end FreeProbability.Fock
