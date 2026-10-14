import FreeProbability.RandomMatrix.OrthogonalPairingCycleCount
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Logic.Equiv.Fin.Rotate

/-! # Actual finite permutation orbit enumeration and network factorization -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal
open Equiv.Perm
variable {α : Type*} [Fintype α] (σ : Equiv.Perm α)

abbrev PermutationOrbitIndex := Quotient (SameCycle.setoid σ)
abbrev PermutationOrbit (c : PermutationOrbitIndex σ) := {a : α // SameCycle σ c.out a}

def permutationOrbitFinset (c : PermutationOrbitIndex σ) : Finset α :=
  Finset.univ.filter (fun a => SameCycle σ c.out a)

theorem permutationOrbit_card (c : PermutationOrbitIndex σ) :
    Fintype.card (PermutationOrbit σ c) = (permutationOrbitFinset σ c).card :=
  Fintype.card_subtype _

private theorem orbit_isCycleOn (c : PermutationOrbitIndex σ) :
    σ.IsCycleOn (permutationOrbitFinset σ c : Set α) := by
  constructor
  · refine ⟨?_, σ.injective.injOn, ?_⟩
    · intro a ha
      simp only [permutationOrbitFinset, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
        true_and] at ha ⊢
      exact ha.apply_right
    · intro a ha
      refine ⟨σ.symm a, ?_, σ.apply_symm_apply a⟩
      simp only [permutationOrbitFinset, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
        true_and] at ha ⊢
      exact ha.symm_apply_right
  · intro a ha b hb
    simp only [permutationOrbitFinset, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and] at ha hb
    exact ha.symm.trans hb

private theorem orbit_seed_mem (c : PermutationOrbitIndex σ) :
    c.out ∈ permutationOrbitFinset σ c := by
  simp [permutationOrbitFinset, SameCycle.refl]

/-- Every indexed actual orbit has positive length, including singleton cycles. -/
theorem permutationOrbit_length_pos (c : PermutationOrbitIndex σ) :
    0 < (permutationOrbitFinset σ c).card := Finset.card_pos.mpr ⟨c.out, orbit_seed_mem σ c⟩

/-- Enumeration by ACTUAL permutation powers, with no supplied cycle witness. -/
def permutationOrbitEnumeration (c : PermutationOrbitIndex σ) :
    Fin (permutationOrbitFinset σ c).card ≃ PermutationOrbit σ c :=
  Equiv.ofBijective (fun k => ⟨(σ ^ k.val) c.out,
    ⟨(k.val : ℤ), by simp only [zpow_natCast]⟩⟩) (by
      constructor
      · intro k l h
        apply Fin.ext
        have he := (orbit_isCycleOn σ c).pow_apply_eq_pow_apply (orbit_seed_mem σ c)
          |>.mp (congrArg Subtype.val h)
        exact he.eq_of_lt_of_lt k.isLt l.isLt
      · intro a
        have ha : a.val ∈ permutationOrbitFinset σ c := by
          simp only [permutationOrbitFinset, Finset.mem_filter, Finset.mem_univ, true_and]
          exact a.property
        obtain ⟨k, hk, he⟩ := (orbit_isCycleOn σ c).exists_pow_eq (orbit_seed_mem σ c) ha
        exact ⟨⟨k, hk⟩, Subtype.ext he⟩)

theorem permutationOrbitEnumeration_apply (c : PermutationOrbitIndex σ)
    (k : Fin (permutationOrbitFinset σ c).card) :
    (permutationOrbitEnumeration σ c k).val = (σ ^ k.val) c.out := rfl

private theorem rotation_value {l : ℕ} (hl : 0 < l) (k : Fin l) :
    (finRotate l k).val = if k.val + 1 = l then 0 else k.val + 1 := by
  cases l with
  | zero => omega
  | succ m =>
    rw [coe_finRotate]
    have he : k = Fin.last m ↔ k.val + 1 = m + 1 := by simp only [Fin.ext_iff, Fin.val_last]; omega
    simp only [he]

/-- The enumeration truly closes and follows the actual permutation at each
cyclic successor, also in length one. -/
theorem permutationOrbitEnumeration_rotate (c : PermutationOrbitIndex σ)
    (k : Fin (permutationOrbitFinset σ c).card) :
    (permutationOrbitEnumeration σ c (finRotate _ k)).val =
      σ (permutationOrbitEnumeration σ c k).val := by
  rw [permutationOrbitEnumeration_apply, permutationOrbitEnumeration_apply]
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (permutationOrbit_length_pos σ c))
  have hk : k.val = m ∨ k.val < m := by omega
  rcases hk with hk | hk
  · have hrot : (finRotate _ k).val = 0 := by
      rw [rotation_value (permutationOrbit_length_pos σ c)]
      simp only [hk, hm, ite_true]
    rw [hrot, pow_zero, Equiv.Perm.one_apply]
    have he := (orbit_isCycleOn σ c).pow_card_apply (orbit_seed_mem σ c)
    rw [hm, pow_succ', Equiv.Perm.mul_apply] at he
    simpa only [hk] using he.symm
  · have hrot : (finRotate _ k).val = k.val + 1 := by
      rw [rotation_value (permutationOrbit_length_pos σ c)]
      have hne : k.val + 1 ≠ (permutationOrbitFinset σ c).card := by omega
      simp only [hne, ite_false]
    rw [hrot, pow_succ', Equiv.Perm.mul_apply]

/-- Actual sites partition into their genuine orbit fibers. -/
def permutationOrbitSigmaEquiv : (Σ c : PermutationOrbitIndex σ, PermutationOrbit σ c) ≃ α where
  toFun s := s.2.val
  invFun a := ⟨Quotient.mk _ a, a, Quotient.exact (Quotient.out_eq (Quotient.mk (SameCycle.setoid σ) a))⟩
  left_inv s := by
    rcases s with ⟨c, a, ha⟩
    have hc : (Quotient.mk _ a : PermutationOrbitIndex σ) = c :=
      (Quotient.sound ha).symm.trans (Quotient.out_eq c)
    cases hc
    rfl
  right_inv a := rfl

/-- Arbitrary site colorings are genuinely independent colorings of all orbits. -/
def permutationOrbitColoringsEquiv (n : Type*) : (α → n) ≃
    (∀ c : PermutationOrbitIndex σ, PermutationOrbit σ c → n) :=
  (Equiv.arrowCongr (permutationOrbitSigmaEquiv σ).symm (Equiv.refl n)).trans
    (Equiv.piCurry (fun (_ : PermutationOrbitIndex σ) (_ : PermutationOrbit σ _) => n))

/-- The actual successor inside an orbit. -/
def permutationOrbitNext (c : PermutationOrbitIndex σ) (a : PermutationOrbit σ c) :
    PermutationOrbit σ c := ⟨σ a.val, a.property.apply_right⟩

omit [Fintype α] in
private theorem orbit_colorings_inverse_apply {n : Type*}
    (g : ∀ c : PermutationOrbitIndex σ, PermutationOrbit σ c → n)
    (c : PermutationOrbitIndex σ) (a : PermutationOrbit σ c) :
    (permutationOrbitColoringsEquiv σ n).symm g a.val = g c a := by
  exact congrFun (congrFun ((permutationOrbitColoringsEquiv σ n).apply_symm_apply g) c) a

/-- The genuine finite network of complex matrix entries along a permutation. -/
def permutationNetwork {n : Type*} [Fintype n] (M : α → Matrix n n ℂ) : ℂ :=
  ∑ u : α → n, ∏ a, M a (u a) (u (σ a))

/-- The actual finite network restricted to one genuine orbit. -/
def permutationOrbitNetwork {n : Type*} [Fintype n] (M : α → Matrix n n ℂ)
    (c : PermutationOrbitIndex σ) : ℂ :=
  ∑ v : PermutationOrbit σ c → n, ∏ a : PermutationOrbit σ c,
    M a.val (v a) (v (permutationOrbitNext σ c a))

/-- Independent orbit colorings genuinely factor the actual network sum.
Fixed singleton cycles are retained, and no trace formula is assumed. -/
theorem permutationNetwork_eq_prod_orbit_networks {n : Type*} [Fintype n]
    (M : α → Matrix n n ℂ) :
    permutationNetwork σ M = ∏ c : PermutationOrbitIndex σ, permutationOrbitNetwork σ M c := by
  unfold permutationNetwork
  rw [← Equiv.sum_comp (permutationOrbitColoringsEquiv σ n).symm]
  have he (g : ∀ c : PermutationOrbitIndex σ, PermutationOrbit σ c → n) :
      (∏ a, M a ((permutationOrbitColoringsEquiv σ n).symm g a)
        ((permutationOrbitColoringsEquiv σ n).symm g (σ a))) =
      ∏ c : PermutationOrbitIndex σ, ∏ a : PermutationOrbit σ c,
        M a.val (g c a) (g c (permutationOrbitNext σ c a)) := by
    rw [← Equiv.prod_comp (permutationOrbitSigmaEquiv σ), Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro c _
    apply Finset.prod_congr rfl
    intro a _
    change M a.val ((permutationOrbitColoringsEquiv σ n).symm g a.val)
      ((permutationOrbitColoringsEquiv σ n).symm g (σ a.val)) = _
    rw [orbit_colorings_inverse_apply]
    have hs := orbit_colorings_inverse_apply σ g c (permutationOrbitNext σ c a)
    change (permutationOrbitColoringsEquiv σ n).symm g (σ a.val) = _ at hs
    rw [hs]
  simp_rw [he]
  exact (Fintype.prod_sum (fun (c : PermutationOrbitIndex σ) (v : PermutationOrbit σ c → n) =>
    ∏ a : PermutationOrbit σ c, M a.val (v a) (v (permutationOrbitNext σ c a)))).symm

end FreeProbability.Orthogonal
