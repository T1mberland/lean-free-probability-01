import FreeProbability.Fock.OrnsteinUhlenbeckDilationVectorWick
import FreeProbability.Fock.WickProductNormalOrder

/-! # Actual canonical Wick-polynomial degree scaling under the Fock rotation dilation -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Canonical creators and the original-H tensor creators are exactly unitarily transported. -/
theorem ou_tensorCreation_basis (i : fullFockBasisSet H) :
    tensorCreation H (fullFockBasis H i) = tensorOperatorEquiv H (creation i) := by
  change tensorOperatorEquiv H (basisCreation (fullFockBasis H) (fullFockBasis H i)) = _
  rw [basisCreation_basis]

theorem ou_tensorAnnihilation_basis (i : fullFockBasisSet H) :
    tensorAnnihilation H (fullFockBasis H i) = tensorOperatorEquiv H (annihilation i) := by
  change star (tensorCreation H (fullFockBasis H i)) = tensorOperatorEquiv H (star (creation i))
  rw [ou_tensorCreation_basis, map_star]

theorem tensorCreatorWord_basis_transport (w : List (fullFockBasisSet H)) :
    tensorCreatorWord (w.map (fullFockBasis H)) = tensorOperatorEquiv H (creationWord w) := by
  induction w with
  | nil => simp
  | cons i w ih =>
    simp only [List.map_cons, tensorCreatorWord_cons, creationWord_cons, map_mul,
      ou_tensorCreation_basis, ih]

theorem tensorAnnihilatorWord_basis_transport (w : List (fullFockBasisSet H)) :
    tensorAnnihilatorWord (w.map (fullFockBasis H)) = tensorOperatorEquiv H (annihilationWord w) := by
  induction w with
  | nil => simp
  | cons i w ih =>
    simp only [List.map_cons, tensorAnnihilatorWord_cons, annihilationWord_cons, map_mul,
      ou_tensorAnnihilation_basis, ih]

/-- Genuine recursive vector Wick operators equal the established canonical Wick polynomials. -/
theorem tensorVectorWick_basis_transport (w : List (fullFockBasisSet H)) :
    tensorVectorWick (w.map (fullFockBasis H)) = tensorOperatorEquiv H (wick w) := by
  rw [tensorVectorWick_eq_normalOrder, wick_normal_order_expansion, map_sum]
  unfold tensorNormalOrder
  have hl : (w.map (fullFockBasis H)).length = w.length := List.length_map _
  rw [hl]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_mul, ← tensorCreatorWord_basis_transport, ← tensorAnnihilatorWord_basis_transport]
  congr 1 <;> simp

/-- The genuine second-quantized unitary conjugates the complete recursive Wick polynomial. -/
theorem secondQuantization_conj_vectorWick (U : H ≃ₗᵢ[ℂ] H) (w : List H) :
    (secondQuantization U).conjStarAlgEquiv (tensorVectorWick w) = tensorVectorWick (w.map U) := by
  induction w using List.twoStepInduction with
  | nil => simp [tensorVectorWick]
  | singleton h =>
    simp only [tensorVectorWick, List.map_cons, List.map_nil, mul_one, sub_zero,
      map_add, secondQuantization_conj_creation, secondQuantization_conj_annihilation]
  | cons_cons h k w h₁ h₂ =>
    change (secondQuantization U).conjStarAlgEquiv
      ((tensorCreation H h + tensorAnnihilation H h) * tensorVectorWick (k :: w) -
        inner ℂ h k • tensorVectorWick w) =
      (tensorCreation H (U h) + tensorAnnihilation H (U h)) * tensorVectorWick (U k :: w.map U) -
        inner ℂ (U h) (U k) • tensorVectorWick (w.map U)
    rw [map_sub, map_mul, map_add, secondQuantization_conj_creation,
      secondQuantization_conj_annihilation, h₂ k, map_smul, h₁, U.inner_map_map]
    rfl

/-- The actual rotated compression of an included recursive vector Wick polynomial has degree factor rⁿ. -/
theorem rotatedFockCompression_vectorWick_first (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) (w : List H) :
    rotatedFockCompression H r s hrs (tensorVectorWick (w.map (doubledFirst H))) =
      (r : ℂ) ^ w.length • tensorVectorWick w := by
  rw [rotatedFockCompression_apply]
  change secondQuantizationCompression (doubledFirst H)
    ((secondQuantization (doubledRotation r s hrs)).conjStarAlgEquiv
      (tensorVectorWick (w.map (doubledFirst H)))) = _
  rw [secondQuantization_conj_vectorWick]
  have hw : (w.map (doubledFirst H)).map (doubledRotation r s hrs) = rotatedFirstWord r s hrs w := by
    simp [rotatedFirstWord, List.map_map, Function.comp_def]
  rw [hw]
  exact rotated_tensorVectorWick_compression r s hrs w

/-- Literal existing canonical Wick polynomial, transported on the exact original-H tensor domain,
with actual included Wick-polynomial input and actual CP rotation compression. -/
theorem rotatedFockCompression_canonicalWick (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1)
    (w : List (fullFockBasisSet H)) :
    rotatedFockCompression H r s hrs
      (tensorVectorWick ((w.map (fullFockBasis H)).map (doubledFirst H))) =
      (r : ℂ) ^ w.length • tensorOperatorEquiv H (wick w) := by
  rw [rotatedFockCompression_vectorWick_first, tensorVectorWick_basis_transport, List.length_map]

/-- At nonnegative time the actual canonical Wick degree multiplier is (e⁻ᵗ)ⁿ. -/
theorem ouTimeDilation_canonicalWick (t : ℝ) (ht : 0 ≤ t) (w : List (fullFockBasisSet H)) :
    ouTimeDilation H t ht
      (tensorVectorWick ((w.map (fullFockBasis H)).map (doubledFirst H))) =
      (Real.exp (-t) : ℂ) ^ w.length • tensorOperatorEquiv H (wick w) :=
  rotatedFockCompression_canonicalWick _ _ _ w

end FreeProbability.Fock
