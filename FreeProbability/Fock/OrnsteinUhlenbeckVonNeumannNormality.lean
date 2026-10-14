import FreeProbability.OperatorValued.OperatorBoundedWOTSupremum
import FreeProbability.Fock.OrnsteinUhlenbeckVonNeumannIntrinsicTime
import FreeProbability.Fock.OrnsteinUhlenbeckVonNeumannRangeWOT

/-! # Actual directed-positive-supremum normality of the intrinsic OU maps -/
noncomputable section
open scoped NNReal Topology
open Filter
namespace FreeProbability.Fock
attribute [local irreducible] fullFockTensorDecomposition isometryPrefixTargetUnitary
  isometrySuffixEmbedding wordSuffixEmbedding doubledRotation secondQuantization isometryPrefixEmbedding
  doubledFockRotation doubledFirst doubledSecond fullFockBasis tensorCreation tensorAnnihilation tensorFamilyField
variable {J I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance (e : I → H) : PartialOrder (tensorFamilyDoubleAlgebra e) := tensorFamilyDoubleAlgebraOrder e
local instance (e : I → H) : Preorder (tensorFamilyDoubleAlgebra e) := (tensorFamilyDoubleAlgebraOrder e).toPreorder
local instance (e : I → H) : LE (tensorFamilyDoubleAlgebra e) := (tensorFamilyDoubleAlgebraOrder e).toLE

/-- Canonical order on the actual closed algebra agrees with the genuine ambient Loewner order. -/
theorem tensorFamilyDoubleAlgebra_coe_le_iff (e : I → H) (A B : tensorFamilyDoubleAlgebra e) :
    (A : TensorFullFock H →L[ℂ] TensorFullFock H) ≤ B ↔ A ≤ B :=
  NonUnitalStarAlgHom.map_le_map_iff (tensorFamilyDoubleAlgebra e).subtype.toNonUnitalStarAlgHom
    Subtype.val_injective

/-- The canonical Cstar order is exactly the order inherited from the ambient operators. -/
theorem tensorFamilyDoubleAlgebra_order_eq_inherited (e : I → H) :
    tensorFamilyDoubleAlgebraOrder e =
      Subtype.partialOrder (fun T : TensorFullFock H →L[ℂ] TensorFullFock H => T ∈ tensorFamilyDoubleAlgebra e) := by
  apply PartialOrder.ext
  intro A B
  exact (tensorFamilyDoubleAlgebra_coe_le_iff e A B).symm

/-- An intrinsic bounded monotone supremum is the actual ambient strong supremum. -/
theorem tensorFamilyDoubleAlgebra_isLUB_coe [Preorder J] [NeBot (atTop : Filter J)]
    (e : I → H) (T : J → tensorFamilyDoubleAlgebra e) (hT : Monotone T)
    (C : ℝ≥0) (hn : ∀ j, ‖T j‖ ≤ C) (S : tensorFamilyDoubleAlgebra e)
    (hS : IsLUB (Set.range T) S) :
    IsLUB (Set.range (fun j => (T j : TensorFullFock H →L[ℂ] TensorFullFock H)))
      (S : TensorFullFock H →L[ℂ] TensorFullFock H) := by
  have hmono : Monotone (fun j => (T j : TensorFullFock H →L[ℂ] TensorFullFock H)) :=
    fun i j hij => (tensorFamilyDoubleAlgebra_coe_le_iff e _ _).mpr (hT hij)
  have hm (j : J) : (T j : TensorFullFock H →L[ℂ] TensorFullFock H) ∈
      (Set.range (tensorFamilyField e)).centralizer.centralizer := by
    rw [← tensorFamilyDoubleAlgebra_coe]
    exact (T j).property
  obtain ⟨R, hRm, hR, _, _⟩ := operatorDoubleCentralizer_exists_isLUB
    (Set.range (tensorFamilyField e)) _ hmono hm C hn
  let r : tensorFamilyDoubleAlgebra e := ⟨R, by
    change R ∈ (tensorFamilyDoubleAlgebra e : Set (TensorFullFock H →L[ℂ] TensorFullFock H))
    rw [tensorFamilyDoubleAlgebra_coe]
    exact hRm⟩
  have hr : IsLUB (Set.range T) r := by
    constructor
    · rintro _ ⟨j, rfl⟩
      exact (tensorFamilyDoubleAlgebra_coe_le_iff e _ _).mp (hR.1 ⟨j, rfl⟩)
    · intro B hB
      apply (tensorFamilyDoubleAlgebra_coe_le_iff e r B).mp
      apply hR.2
      rintro _ ⟨j, rfl⟩
      exact (tensorFamilyDoubleAlgebra_coe_le_iff e _ _).mpr (hB ⟨j, rfl⟩)
  have he : R = (S : TensorFullFock H →L[ℂ] TensorFullFock H) :=
    congrArg (fun A : tensorFamilyDoubleAlgebra e =>
      (A : TensorFullFock H →L[ℂ] TensorFullFock H)) (hr.unique hS)
  rwa [he] at hR

/-- Actual ambient OU rotation-compression preserves every bounded increasing directed supremum. -/
theorem ouDoubleCommutantRawCP_isLUB [Preorder J] [NeBot (atTop : Filter J)]
    (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1)
    (T : J → (TensorFullFock H →L[ℂ] TensorFullFock H)) (hT : Monotone T)
    (C : ℝ≥0) (hn : ∀ j, ‖T j‖ ≤ C)
    (S : TensorFullFock H →L[ℂ] TensorFullFock H) (hS : IsLUB (Set.range T) S) :
    IsLUB (Set.range (fun j => ouDoubleCommutantRawCP r s hrs (T j)))
      (ouDoubleCommutantRawCP r s hrs S) :=
  operator_isLUB_map_of_boundedWOT_continuous (ouDoubleCommutantRawCP r s hrs)
    (OrderHomClass.monotone _) (norm_ouDoubleCommutantRawCP_le r s hrs)
    (ouDoubleCommutantRawCP_boundedWOT_continuous r s hrs) T hT C hn S hS

/-- Genuine intrinsic normality: every increasing positive directed supremum is preserved, without an extra norm-bound premise. -/
theorem ouVonNeumannCP_isLUB [Preorder J] [NeBot (atTop : Filter J)]
    (e : I → H) (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1)
    (T : J → tensorFamilyDoubleAlgebra e) (hT : Monotone T) (hp : ∀ j, 0 ≤ T j)
    (S : tensorFamilyDoubleAlgebra e) (hS : IsLUB (Set.range T) S) :
    IsLUB (Set.range (fun j => ouVonNeumannCP e r s hrs (T j)))
      (ouVonNeumannCP e r s hrs S) := by
  have hn (j : J) : ‖T j‖ ≤ ‖S‖₊ :=
    CStarAlgebra.norm_le_norm_of_le_of_nonneg (hS.1 ⟨j, rfl⟩) (hp j)
  have hmono : Monotone (fun j => (T j : TensorFullFock H →L[ℂ] TensorFullFock H)) :=
    fun i j hij => (tensorFamilyDoubleAlgebra_coe_le_iff e _ _).mpr (hT hij)
  have hraw := ouDoubleCommutantRawCP_isLUB r s hrs _ hmono ‖S‖₊ hn _
    (tensorFamilyDoubleAlgebra_isLUB_coe e T hT ‖S‖₊ hn S hS)
  constructor
  · rintro _ ⟨j, rfl⟩
    apply (tensorFamilyDoubleAlgebra_coe_le_iff e
      (ouVonNeumannCP e r s hrs (T j)) (ouVonNeumannCP e r s hrs S)).mp
    simp only [ouVonNeumannCP_coe]
    exact hraw.1 ⟨j, rfl⟩
  · intro B hB
    apply (tensorFamilyDoubleAlgebra_coe_le_iff e (ouVonNeumannCP e r s hrs S) B).mp
    rw [ouVonNeumannCP_coe]
    apply hraw.2
    rintro _ ⟨j, rfl⟩
    have hh := (tensorFamilyDoubleAlgebra_coe_le_iff e (ouVonNeumannCP e r s hrs (T j)) B).mpr
      (hB ⟨j, rfl⟩)
    rwa [ouVonNeumannCP_coe] at hh

/-- The actual nonnegative-time OU maps are normal on every specified-field von Neumann algebra. -/
theorem ouVonNeumannTimeCP_isLUB [Preorder J] [NeBot (atTop : Filter J)]
    (e : I → H) (t : ℝ) (ht : 0 ≤ t) (T : J → tensorFamilyDoubleAlgebra e)
    (hT : Monotone T) (hp : ∀ j, 0 ≤ T j) (S : tensorFamilyDoubleAlgebra e)
    (hS : IsLUB (Set.range T) S) :
    IsLUB (Set.range (fun j => ouVonNeumannTimeCP e t ht (T j)))
      (ouVonNeumannTimeCP e t ht S) :=
  ouVonNeumannCP_isLUB e _ _ _ T hT hp S hS
end FreeProbability.Fock
