import FreeProbability.Combinatorics.ConsecutiveFusion
import Mathlib.Order.Preorder.Finite

/-! # Every ordered interval quotient has a consecutive fusion plan -/

namespace FreeProbability.ConsecutiveFusion

/-- A monotone surjective quotient of finite words is implemented by successive
adjacent fusions. Thus fusion plans cover every ordered grouping into nonempty
consecutive intervals, not merely a selected family of groupings. -/
theorem exists_quotient_eq {n m : ℕ} (f : Fin n → Fin m)
    (hf : Monotone f) (hs : Function.Surjective f) :
    ∃ t : ConsecutiveFusion n m, t.quotient = f := by
  induction n generalizing m with
  | zero =>
    have hm : m = 0 := by
      have hc := Fintype.card_le_of_surjective f hs
      simp only [Fintype.card_fin] at hc
      omega
    subst m
    exact ⟨.refl 0, funext (fun a => Fin.elim0 a)⟩
  | succ n ih =>
    by_cases hinj : Function.Injective f
    · have hm : m = n + 1 := by
        have hc := Fintype.card_of_bijective ⟨hinj, hs⟩
        simpa only [Fintype.card_fin] using hc.symm
      subst m
      exact ⟨.refl _, (hf.strictMono_of_injective hinj).eq_id.symm⟩
    · have hpair : ∃ i : Fin n, f i.castSucc = f i.succ := by
        by_contra h
        push Not at h
        apply hinj
        exact (Fin.strictMono_iff_lt_succ.mpr (fun i =>
          lt_of_le_of_ne (hf (Fin.castSucc_lt_succ.le)) (h i))).injective
      obtain ⟨i, hi⟩ := hpair
      let g : Fin n → Fin m := fun a => f (i.castSucc.succAbove a)
      have hg : Monotone g := hf.comp i.castSucc.strictMono_succAbove.monotone
      have he (a : Fin (n + 1)) : g (i.predAbove a) = f a := by
        by_cases ha : a = i.castSucc
        · subst a
          simpa only [g, Fin.predAbove_castSucc_self, Fin.succAbove_castSucc_self] using hi.symm
        · simp only [g, Fin.succAbove_predAbove ha]
      have hgs : Function.Surjective g := by
        intro a
        obtain ⟨b, hb⟩ := hs a
        exact ⟨i.predAbove b, (he b).trans hb⟩
      obtain ⟨t, ht⟩ := ih g hg hgs
      refine ⟨.cons i t, funext (fun a => ?_)⟩
      change t.quotient (i.predAbove a) = f a
      rw [ht]
      exact he a

end FreeProbability.ConsecutiveFusion
