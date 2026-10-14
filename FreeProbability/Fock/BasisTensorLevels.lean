import FreeProbability.Fock.TensorLevels

/-!
# Completed tensor levels for an arbitrary Hilbert space with a chosen basis

The completed tensor recursion is transported through a genuine Hilbert-basis
isometry. Thus the word model is a Hilbert sum of completed tensor levels of the
original space, and its creation operators literally tensor by the original
vectors. The chosen basis is explicit; no traciality is asserted for all complex
vectors.
-/

noncomputable section
open scoped Classical InnerProductSpace TensorProduct
open UniformSpace

namespace FreeProbability.Fock

section CompletionTransport

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A genuine linear isometric equivalence extends to the Hilbert completions. -/
def isometryEquivCompletion (f : E ≃ₗᵢ[ℂ] F) : Completion E ≃ₗᵢ[ℂ] Completion F where
  toLinearEquiv :=
    { toLinearMap := f.toContinuousLinearEquiv.toContinuousLinearMap.completion.toLinearMap
      invFun := f.symm.toContinuousLinearEquiv.toContinuousLinearMap.completion
      left_inv := by
        intro x
        induction x using Completion.induction_on with
        | hp =>
          exact isClosed_eq
            (f.symm.toContinuousLinearEquiv.toContinuousLinearMap.completion.continuous.comp
              f.toContinuousLinearEquiv.toContinuousLinearMap.completion.continuous) continuous_id
        | ih x => simp
      right_inv := by
        intro x
        induction x using Completion.induction_on with
        | hp =>
          exact isClosed_eq
            (f.toContinuousLinearEquiv.toContinuousLinearMap.completion.continuous.comp
              f.symm.toContinuousLinearEquiv.toContinuousLinearMap.completion.continuous) continuous_id
        | ih x => simp }
  norm_map' := by
    intro x
    induction x using Completion.induction_on with
    | hp =>
      exact isClosed_eq
        (continuous_norm.comp f.toContinuousLinearEquiv.toContinuousLinearMap.completion.continuous)
        continuous_norm
    | ih x => simp

@[simp] theorem isometryEquivCompletion_coe (f : E ≃ₗᵢ[ℂ] F) (x : E) :
    isometryEquivCompletion f (x : Completion E) = (f x : Completion F) :=
  ContinuousLinearMap.completion_apply_coe _ x

end CompletionTransport

variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The next word level is the actual completed tensor product with the original space. -/
def basisSuccessorLevelTensorEquiv (b : HilbertBasis I ℂ H) (n : ℕ) :
    Completion (H ⊗[ℂ] WordLevel I n) ≃ₗᵢ[ℂ] WordLevel I (n + 1) :=
  (isometryEquivCompletion (TensorProduct.congrIsometry b.repr
    (LinearIsometryEquiv.refl ℂ (WordLevel I n)))).trans (successorLevelTensorEquiv n)

/-- The genuine tensor recursion also carries the bounded creation operators. -/
theorem basisLevelEmbedding_tensorCreation (b : HilbertBasis I ℂ H) (n : ℕ)
    (h : H) (f : WordLevel I n) :
    levelEmbedding (n + 1) (basisSuccessorLevelTensorEquiv b n
      ((h ⊗ₜ[ℂ] f : H ⊗[ℂ] WordLevel I n) : Completion (H ⊗[ℂ] WordLevel I n))) =
      basisCreation b h (levelEmbedding n f) := by
  change levelEmbedding (n + 1) (successorLevelTensorEquiv n
    (isometryEquivCompletion _ _)) = _
  rw [isometryEquivCompletion_coe]
  simp only [TensorProduct.congrIsometry_apply, TensorProduct.congr_tmul]
  exact levelEmbedding_tensorCreation n (b.repr h) f

end FreeProbability.Fock
