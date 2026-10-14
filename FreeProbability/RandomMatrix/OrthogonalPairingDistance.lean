import FreeProbability.RandomMatrix.OrthogonalPairingLoopBounds
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # The genuine ordinary pairing distance -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal

private def constantSubspace {α : Type*} (s : Setoid α) : Submodule ℝ (α → ℝ) where
  carrier := {f | ∀ a b, s.r a b → f a = f b}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg a b hab; simp only [Pi.add_apply, hf a b hab, hg a b hab]
  smul_mem' := by intro c f hf a b hab; simp only [Pi.smul_apply, hf a b hab]

private def quotientPullback {α : Type*} (s : Setoid α) :
    (Quotient s → ℝ) →ₗ[ℝ] (α → ℝ) where
  toFun f a := f (Quotient.mk s a)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

private theorem quotientPullback_injective {α : Type*} (s : Setoid α) :
    Function.Injective (quotientPullback s) := by
  intro f g h
  funext a
  induction a using Quotient.inductionOn with
  | h a => exact congrFun h a

private theorem quotientPullback_range {α : Type*} (s : Setoid α) :
    LinearMap.range (quotientPullback s) = constantSubspace s := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩ a b hab
    change g (Quotient.mk s a) = g (Quotient.mk s b)
    rw [Quotient.sound hab]
  · intro hf
    exact ⟨Quotient.lift f (fun a b hab => hf a b hab), rfl⟩

private theorem finrank_constantSubspace {α : Type*} [Fintype α] (s : Setoid α) :
    Module.finrank ℝ (constantSubspace s) = Fintype.card (Quotient s) := by
  rw [← quotientPullback_range, LinearMap.finrank_range_of_inj (quotientPullback_injective s)]
  exact Module.finrank_pi ℝ

private theorem constantSubspace_sup {α : Type*} (s t : Setoid α) :
    constantSubspace (s ⊔ t) = constantSubspace s ⊓ constantSubspace t := by
  ext f
  change (s ⊔ t ≤ Setoid.ker f) ↔ (s ≤ Setoid.ker f ∧ t ≤ Setoid.ker f)
  exact sup_le_iff

/-- A genuine finite-partition inequality obtained from dimensions of spaces
of functions constant on the raw equivalence classes. -/
theorem card_quotient_join_triangle {α : Type*} [Fintype α] (p q s : Setoid α) :
    Fintype.card (Quotient (p ⊔ q)) + Fintype.card (Quotient (q ⊔ s)) ≤
      Fintype.card (Quotient q) + Fintype.card (Quotient (p ⊔ s)) := by
  let X := constantSubspace p ⊓ constantSubspace q
  let Y := constantSubspace q ⊓ constantSubspace s
  have hsup : X ⊔ Y ≤ constantSubspace q := sup_le inf_le_right inf_le_left
  have hinf : X ⊓ Y ≤ constantSubspace p ⊓ constantSubspace s :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right)
  have hs := Submodule.finrank_mono hsup
  have hi := Submodule.finrank_mono hinf
  have hd := Submodule.finrank_sup_add_finrank_inf_eq X Y
  rw [← constantSubspace_sup] at hi
  rw [finrank_constantSubspace] at hs hi
  have heX : Module.finrank ℝ X = Fintype.card (Quotient (p ⊔ q)) := by
    exact (congrArg (fun S : Submodule ℝ (α → ℝ) => Module.finrank ℝ S)
      (constantSubspace_sup p q)).symm.trans (finrank_constantSubspace (p ⊔ q))
  have heY : Module.finrank ℝ Y = Fintype.card (Quotient (q ⊔ s)) := by
    exact (congrArg (fun S : Submodule ℝ (α → ℝ) => Module.finrank ℝ S)
      (constantSubspace_sup q s)).symm.trans (finrank_constantSubspace (q ⊔ s))
  omega

/-- The distance uses the ORDINARY raw join, including crossing pairings. -/
def pairingDistance {r : ℕ} (p q : OrdinaryPairing r) : ℕ := r - pairingLoopCount p q

theorem pairingDistance_eq_zero_iff {r : ℕ} (p q : OrdinaryPairing r) :
    pairingDistance p q = 0 ↔ p = q := by
  rw [pairingDistance, Nat.sub_eq_zero_iff_le]
  exact ⟨fun h => (pairingLoopCount_eq_iff p q).mp (le_antisymm (pairingLoopCount_le p q) h),
    fun h => ((pairingLoopCount_eq_iff p q).mpr h).ge⟩

theorem pairingDistance_comm {r : ℕ} (p q : OrdinaryPairing r) :
    pairingDistance p q = pairingDistance q p := by
  simp only [pairingDistance, pairingLoopCount, sup_comm]

/-- The actual raw pairing distance satisfies the triangle inequality. -/
theorem pairingDistance_triangle {r : ℕ} (p q s : OrdinaryPairing r) :
    pairingDistance p s ≤ pairingDistance p q + pairingDistance q s := by
  have h := card_quotient_join_triangle (pairingSetoid p.out) (pairingSetoid q.out)
    (pairingSetoid s.out)
  rw [card_pairingSetoid_quotient] at h
  change pairingLoopCount p q + pairingLoopCount q s ≤ r + pairingLoopCount p s at h
  have hpq := pairingLoopCount_le p q
  have hqs := pairingLoopCount_le q s
  have hps := pairingLoopCount_le p s
  simp only [pairingDistance]
  omega

end FreeProbability.Orthogonal
