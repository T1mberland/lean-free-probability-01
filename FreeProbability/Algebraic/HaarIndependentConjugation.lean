import FreeProbability.Algebraic.HaarConjugation

/-! # Entire algebra copies conjugated by jointly free Haar unitaries -/

namespace FreeProbability
variable {𝕜 A I : Type*} [Field 𝕜] [StarRing 𝕜] [Ring A] [StarRing A]
  [Algebra 𝕜 A] [StarModule 𝕜 A]

/-- The ENTIRE base algebra and ENTIRE Haar-generated algebras, jointly indexed. -/
def haarIndependentBaseFamily (B : Subalgebra 𝕜 A) (u : I → unitary A) :
    Unit ⊕ I → Subalgebra 𝕜 A
  | .inl _ => B
  | .inr i => haarUnitaryAlgebra (u i)

/-- Joint freeness supplies each full base/Haar pair without a pairwise shortcut. -/
theorem haarIndependentBaseFamily_pair_free (φ : ProbabilitySpace 𝕜 A)
    (B : Subalgebra 𝕜 A) (u : I → unitary A)
    (hf : FreelyIndependent φ (haarIndependentBaseFamily B u)) (i : I) :
    FreelyIndependent φ (haarBasePair (u i) B) := by
  let f : Bool → Unit ⊕ I := fun b => if b then Sum.inr i else Sum.inl ()
  have hinj : Function.Injective f := by
    intro b c he
    cases b <;> cases c <;> simp [f] at he ⊢
  have h := hf.reindex f hinj
  convert h using 1
  funext b
  cases b <;> rfl

/-- Each conjugated base letter expands to three actual letters from the
jointly free family. -/
def haarIndependentExpandedWord (u : I → unitary A) (w : List (I × A)) :
    List ((Unit ⊕ I) × A) :=
  w.flatMap (fun x => [(Sum.inr x.1, (u x.1 : A)), (Sum.inl (), x.2),
    (Sum.inr x.1, star (u x.1 : A))])

omit [StarRing 𝕜] [StarModule 𝕜 A] in
/-- Exact expansion of the complete product of actual conjugates. -/
theorem haarIndependentExpandedWord_product (u : I → unitary A) (w : List (I × A)) :
    ((haarIndependentExpandedWord u w).map Prod.snd).prod =
      (w.map (fun x => haarConjugate (𝕜 := 𝕜) (u x.1) 1 x.2)).prod := by
  induction w with
  | nil => simp [haarIndependentExpandedWord]
  | cons x w ih =>
    simp only [haarIndependentExpandedWord, List.flatMap_cons, List.map_append, List.prod_append,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at ih ⊢
    rw [ih]
    simp only [haarConjugate_eq, unitaryPower_one, unitaryPower_neg, mul_assoc]

/-- Adjacent DIFFERENT conjugators keep their two adjacent Haar letters in
DIFFERENT free algebras. Nonadjacent repetitions remain allowed. -/
theorem haarIndependentExpandedWord_isChain (u : I → unitary A) (w : List (I × A))
    (hw : w.IsChain (fun x y => x.1 ≠ y.1)) :
    (haarIndependentExpandedWord u w).IsChain (fun x y => x.1 ≠ y.1) := by
  induction w with
  | nil => simp [haarIndependentExpandedWord]
  | cons x w ih =>
    cases w with
    | nil => simp [haarIndependentExpandedWord]
    | cons y w =>
      have hxy := List.isChain_cons_cons.mp hw
      have ht := ih hxy.2
      simpa [haarIndependentExpandedWord, List.isChain_cons_cons] using
        And.intro hxy.1 ht

theorem haarIndependentExpandedWord_ne_nil (u : I → unitary A) {w : List (I × A)} (hw : w ≠ []) :
    haarIndependentExpandedWord u w ≠ [] := by
  cases w with
  | nil => exact False.elim (hw rfl)
  | cons x w => simp [haarIndependentExpandedWord]

/-- Full centered alternating products vanish under JOINT freeness of the
entire base algebra and every entire Haar-generated algebra. -/
theorem expectation_independentHaarConjugates_prod_eq_zero (φ : ProbabilitySpace 𝕜 A)
    (B : Subalgebra 𝕜 A) (u : I → unitary A) (hu : ∀ i, IsHaarUnitary φ (u i))
    (hf : FreelyIndependent φ (haarIndependentBaseFamily B u)) (w : List (I × A))
    (hw : w ≠ []) (hchain : w.IsChain (fun x y => x.1 ≠ y.1))
    (hmem : ∀ x ∈ w, x.2 ∈ B) (hzero : ∀ x ∈ w, φ.expectation x.2 = 0) :
    φ.expectation (w.map (fun x => haarConjugate (𝕜 := 𝕜) (u x.1) 1 x.2)).prod = 0 := by
  rw [← haarIndependentExpandedWord_product]
  have hvalid : ∀ x ∈ haarIndependentExpandedWord u w,
      x.2 ∈ haarIndependentBaseFamily B u x.1 ∧ φ.expectation x.2 = 0 := by
    intro x hx
    obtain ⟨y, hy, hx⟩ := List.mem_flatMap.mp hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨unitaryPower_one (u y.1) ▸ unitaryPower_mem_haarUnitaryAlgebra (u y.1) 1,
        by simpa only [unitaryPower_one] using hu y.1 1 (by norm_num)⟩
    · exact ⟨hmem y hy, hzero y hy⟩
    · exact ⟨by simpa only [unitaryPower_neg, unitaryPower_one, haarIndependentBaseFamily] using
          unitaryPower_mem_haarUnitaryAlgebra (𝕜 := 𝕜) (u y.1) (-1),
        by simpa only [unitaryPower_neg, unitaryPower_one] using hu y.1 (-1) (by norm_num)⟩
  exact hf _ (haarIndependentExpandedWord_ne_nil u hw)
    (haarIndependentExpandedWord_isChain u w hchain)
    (fun x hx => (hvalid x hx).1) (fun x hx => (hvalid x hx).2)

/-- Arbitrarily indexed, including infinite or empty, jointly free Haar
conjugators produce freely independent ENTIRE copies of the base algebra. -/
theorem freelyIndependent_independentHaarConjugatedAlgebras (φ : ProbabilitySpace 𝕜 A)
    (B : Subalgebra 𝕜 A) (u : I → unitary A) (hu : ∀ i, IsHaarUnitary φ (u i))
    (hf : FreelyIndependent φ (haarIndependentBaseFamily B u)) :
    FreelyIndependent φ (fun i => haarConjugatedAlgebra (u i) B 1) := by
  classical
  intro w hw hchain hmem hzero
  let g : I × A → I × A := fun x =>
    (x.1, (Unitary.conjStarAlgAut 𝕜 A (u x.1)).symm x.2)
  have hgmem : ∀ x ∈ w.map g, x.2 ∈ B := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨a, ha, he⟩ := Subalgebra.mem_map.mp (hmem y hy)
    change Unitary.conjStarAlgAut 𝕜 A (u y.1 ^ (1 : ℤ)) a = y.2 at he
    simp only [zpow_one] at he
    change (Unitary.conjStarAlgAut 𝕜 A (u y.1)).symm y.2 ∈ B
    rw [← he, StarAlgEquiv.symm_apply_apply]
    exact ha
  have hrecover (y : I × A) : haarConjugate (𝕜 := 𝕜) (u (g y).1) 1 (g y).2 = y.2 := by
    simp only [g, haarConjugate, zpow_one, StarAlgEquiv.apply_symm_apply]
  have hgzero : ∀ x ∈ w.map g, φ.expectation x.2 = 0 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    have hpres := expectation_haarConjugate φ (u y.1) (hu y.1) B
      (haarIndependentBaseFamily_pair_free φ B u hf y.1) 1
      (hgmem (g y) (List.mem_map.mpr ⟨y, hy, rfl⟩))
    rw [hrecover y] at hpres
    exact hpres.symm.trans (hzero y hy)
  have hgchain : (w.map g).IsChain (fun x y => x.1 ≠ y.1) :=
    (List.isChain_map g).mpr hchain
  have hv := expectation_independentHaarConjugates_prod_eq_zero φ B u hu hf (w.map g)
    (by simpa using hw) hgchain hgmem hgzero
  simpa only [List.map_map, Function.comp_def, hrecover] using hv
end FreeProbability
