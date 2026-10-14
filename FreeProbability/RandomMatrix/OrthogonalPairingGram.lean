import FreeProbability.RandomMatrix.OrthogonalPairingInvariant
import Mathlib.Data.Setoid.Basic

/-! # Actual pairing Gram entries by quotient-coloring cardinalities -/

noncomputable section
open scoped Classical RealInnerProductSpace
namespace FreeProbability.Orthogonal
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The ordinary equivalence relation whose classes are the paired sites. -/
def pairingSetoid {r : ℕ} (e : PairingSites r) : Setoid (Fin (2 * r)) :=
  Setoid.ker (fun p => (e p).1)

omit [Fintype n] [DecidableEq n] in
private theorem pairingSetoid_le_ker_iff {r : ℕ} (e : PairingSites r) (i : Fin (2 * r) → n) :
    pairingSetoid e ≤ Setoid.ker i ↔
      ∀ a : Fin r, i (e.symm (a, 0)) = i (e.symm (a, 1)) := by
  constructor
  · intro h a
    apply h
    change (e (e.symm (a, 0))).1 = (e (e.symm (a, 1))).1
    simp
  · intro h p q hpq
    obtain ⟨⟨a, b⟩, rfl⟩ := e.symm.surjective p
    obtain ⟨⟨c, d⟩, rfl⟩ := e.symm.surjective q
    change (e (e.symm (a, b))).1 = (e (e.symm (c, d))).1 at hpq
    have hac : a = c := by simpa only [Equiv.apply_symm_apply] using hpq
    subst c
    change i (e.symm (a, b)) = i (e.symm (a, d))
    fin_cases b <;> fin_cases d <;> simp [h]

/-- Actual pairing coefficients are indicators of labelings constant on the
ordinary pairing equivalence relation. -/
theorem pairingTensor_coefficient_indicator {r : ℕ} (e : PairingSites r) (i : Fin (2 * r) → n) :
    (pairingTensor (n := n) e) i = if pairingSetoid e ≤ Setoid.ker i then (1 : ℝ) else 0 := by
  rw [pairingTensor_coefficient]
  by_cases h : pairingSetoid e ≤ Setoid.ker i
  · simp only [h, ite_true]
    apply Finset.prod_eq_one
    intro a ha
    simp only [(pairingSetoid_le_ker_iff e i).mp h a, ite_true]
  · simp only [h, ite_false]
    obtain ⟨a, ha⟩ : ∃ a : Fin r, i (e.symm (a, 0)) ≠ i (e.symm (a, 1)) := by
      simpa only [pairingSetoid_le_ker_iff, not_forall] using h
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp [ha])

omit [DecidableEq n] in
/-- A genuine counting identity: compatible tuple labels are precisely maps
from the actual quotient set, with no dimension-genericity assumption. -/
theorem sum_quotient_colorings (k : ℕ) (s : Setoid (Fin k)) :
    (∑ i : Fin k → n, if s ≤ Setoid.ker i then (1 : ℝ) else 0) =
      (Fintype.card n : ℝ) ^ Fintype.card (Quotient s) := by
  rw [Finset.sum_boole]
  have hcard := Fintype.card_subtype (fun i : Fin k → n => s ≤ Setoid.ker i)
  rw [← hcard, Fintype.card_congr (Setoid.liftEquiv s), Fintype.card_fun, Nat.cast_pow]

/-- The genuine Euclidean pairing Gram entry is the dimension raised to the
number of classes of the ORDINARY join, with crossing pairings permitted. -/
theorem pairingTensor_inner {r : ℕ} (e f : PairingSites r) :
    ⟪pairingTensor (n := n) e, pairingTensor (n := n) f⟫ =
      (Fintype.card n : ℝ) ^ Fintype.card (Quotient (pairingSetoid e ⊔ pairingSetoid f)) := by
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply, pairingTensor_coefficient_indicator]
  have hi (i : Fin (2 * r) → n) :
      (if pairingSetoid e ≤ Setoid.ker i then (1 : ℝ) else 0) *
      (if pairingSetoid f ≤ Setoid.ker i then (1 : ℝ) else 0) =
      if pairingSetoid e ⊔ pairingSetoid f ≤ Setoid.ker i then (1 : ℝ) else 0 := by
    rw [sup_le_iff]
    split_ifs <;> simp_all
  simp_rw [hi]
  exact sum_quotient_colorings (n := n) _ _

/-- The actual tensor depends only on the ordinary pairing relation, not its
pair numbering or orientations in a site equivalence. -/
theorem pairingTensor_eq_of_pairingSetoid_eq {r : ℕ} (e f : PairingSites r)
    (h : pairingSetoid e = pairingSetoid f) : pairingTensor (n := n) e = pairingTensor (n := n) f := by
  apply PiLp.ext
  intro i
  simp only [pairingTensor_coefficient_indicator, h]

/-- Each genuine pairing relation has exactly r quotient classes. -/
theorem card_pairingSetoid_quotient {r : ℕ} (e : PairingSites r) :
    Fintype.card (Quotient (pairingSetoid e)) = r := by
  have hs : Function.Surjective (fun p : Fin (2 * r) => (e p).1) := by
    intro a
    exact ⟨e.symm (a, 0), by simp⟩
  change Fintype.card (Quotient (Setoid.ker (fun p : Fin (2 * r) => (e p).1))) = r
  rw [Fintype.card_congr (Setoid.quotientKerEquivOfSurjective (fun p : Fin (2 * r) => (e p).1) hs), Fintype.card_fin]

/-- The squared norm of the ACTUAL pairing tensor is dimension to the number
of pairs, including 0^0 = 1 for the genuine zeroth-order scalar tensor. -/
theorem pairingTensor_norm_sq {r : ℕ} (e : PairingSites r) :
    ‖pairingTensor (n := n) e‖ ^ 2 = (Fintype.card n : ℝ) ^ r := by
  rw [← real_inner_self_eq_norm_sq, pairingTensor_inner, sup_idem, card_pairingSetoid_quotient]
end FreeProbability.Orthogonal
