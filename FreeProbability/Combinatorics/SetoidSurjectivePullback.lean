import Mathlib.Data.Setoid.Basic

/-! # Surjective pullbacks preserve joins of equivalence relations -/

namespace FreeProbability

/-- A surjective quotient lifts every equivalence-join chain, so its pullback
preserves binary joins. Surjectivity is essential for the intermediate chain points. -/
theorem setoid_comap_sup_of_surjective {X Y : Type*} (f : X → Y)
    (hf : Function.Surjective f) (p q : Setoid Y) :
    Setoid.comap f (p ⊔ q) = Setoid.comap f p ⊔ Setoid.comap f q := by
  apply le_antisymm
  · intro a b hab
    rw [Setoid.sup_eq_eqvGen] at hab
    change Relation.EqvGen (fun x y => p.r x y ∨ q.r x y) (f a) (f b) at hab
    have hlift : ∀ u v, Relation.EqvGen (fun x y => p.r x y ∨ q.r x y) u v →
        ∀ a b, f a = u → f b = v → (Setoid.comap f p ⊔ Setoid.comap f q).r a b := by
      intro u v h
      induction h with
      | rel u v huv =>
        intro a b ha hb
        rcases huv with hp | hq
        · exact (show Setoid.comap f p ≤ Setoid.comap f p ⊔ Setoid.comap f q from le_sup_left)
            (by change p.r (f a) (f b); rw [ha, hb]; exact hp)
        · exact (show Setoid.comap f q ≤ Setoid.comap f p ⊔ Setoid.comap f q from le_sup_right)
            (by change q.r (f a) (f b); rw [ha, hb]; exact hq)
      | refl u =>
        intro a b ha hb
        apply (show Setoid.comap f p ≤ Setoid.comap f p ⊔ Setoid.comap f q from le_sup_left)
        change p.r (f a) (f b)
        rw [ha, hb]
      | symm _ _ _ ih =>
        intro a b ha hb
        exact (Setoid.comap f p ⊔ Setoid.comap f q).symm (ih b a hb ha)
      | trans _ c _ _ _ ih₁ ih₂ =>
        intro a b ha hb
        obtain ⟨z, hz⟩ := hf c
        exact (Setoid.comap f p ⊔ Setoid.comap f q).trans (ih₁ a z ha hz) (ih₂ z b hz hb)
    exact hlift _ _ hab a b rfl rfl
  · apply sup_le
    · exact fun _ _ h => (show p ≤ p ⊔ q from le_sup_left) h
    · exact fun _ _ h => (show q ≤ p ⊔ q from le_sup_right) h

end FreeProbability
