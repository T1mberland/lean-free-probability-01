import FreeProbability.Algebraic.HaarConjugationWords

/-! # Freely independent integer conjugated copies of an entire algebra -/

namespace FreeProbability
variable {𝕜 A I : Type*} [Field 𝕜] [StarRing 𝕜] [Ring A] [StarRing A]
  [Algebra 𝕜 A] [StarModule 𝕜 A]

/-- The entire algebra image under a genuine integer-power unitary conjugation. -/
def haarConjugatedAlgebra (u : unitary A) (B : Subalgebra 𝕜 A) (j : ℤ) : Subalgebra 𝕜 A :=
  B.map (Unitary.conjStarAlgAut 𝕜 A (u ^ j)).toAlgEquiv.toAlgHom

/-- All integer-power conjugated copies of the ENTIRE supplied algebra are
freely independent. No trace, positivity or topology is assumed. -/
theorem freelyIndependent_haarConjugatedAlgebras (φ : ProbabilitySpace 𝕜 A)
    (u : unitary A) (hu : IsHaarUnitary φ u) (B : Subalgebra 𝕜 A)
    (hf : FreelyIndependent φ (haarBasePair u B)) :
    FreelyIndependent φ (haarConjugatedAlgebra u B) := by
  classical
  intro w hw hchain hmem hzero
  let g : ℤ × A → ℤ × A := fun x =>
    (x.1, (Unitary.conjStarAlgAut 𝕜 A (u ^ x.1)).symm x.2)
  have hgmem : ∀ x ∈ w.map g, x.2 ∈ B := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨a, ha, he⟩ := Subalgebra.mem_map.mp (hmem y hy)
    change (Unitary.conjStarAlgAut 𝕜 A (u ^ y.1)).symm y.2 ∈ B
    change Unitary.conjStarAlgAut 𝕜 A (u ^ y.1) a = y.2 at he
    rw [← he, StarAlgEquiv.symm_apply_apply]
    exact ha
  have hrecover (y : ℤ × A) : haarConjugate (𝕜 := 𝕜) u (g y).1 (g y).2 = y.2 := by
    simp only [g, haarConjugate, StarAlgEquiv.apply_symm_apply]
  have hgzero : ∀ x ∈ w.map g, φ.expectation x.2 = 0 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    have hpres := expectation_haarConjugate φ u hu B hf y.1 (hgmem (g y) (List.mem_map.mpr ⟨y, hy, rfl⟩))
    rw [show haarConjugate (𝕜 := 𝕜) u y.1 (g y).2 = y.2 from hrecover y] at hpres
    exact hpres.symm.trans (hzero y hy)
  have hgchain : (w.map g).IsChain (fun x y => x.1 ≠ y.1) := by
    exact (List.isChain_map g).mpr hchain
  have hv := expectation_haarConjugates_prod_eq_zero φ u hu B hf (w.map g)
    (by simpa using hw) hgchain hgmem hgzero
  simpa only [List.map_map, Function.comp_def, hrecover] using hv

/-- Any injectively indexed set of integer copies is a free family. -/
theorem freelyIndependent_haarConjugatedAlgebras_reindex (φ : ProbabilitySpace 𝕜 A)
    (u : unitary A) (hu : IsHaarUnitary φ u) (B : Subalgebra 𝕜 A)
    (hf : FreelyIndependent φ (haarBasePair u B)) (f : I → ℤ) (hfinj : Function.Injective f) :
    FreelyIndependent φ (fun i => haarConjugatedAlgebra u B (f i)) :=
  (freelyIndependent_haarConjugatedAlgebras φ u hu B hf).reindex f hfinj

/-- Each complete copy preserves ALL joint moments of elements of the original
algebra without assuming a tracial ambient functional. -/
theorem sameDistribution_haarConjugate (φ : ProbabilitySpace 𝕜 A)
    (u : unitary A) (hu : IsHaarUnitary φ u) (B : Subalgebra 𝕜 A)
    (hf : FreelyIndependent φ (haarBasePair u B)) (j : ℤ) (a : I → A)
    (ha : ∀ i, a i ∈ B) :
    SameDistribution φ φ a (fun i => haarConjugate (𝕜 := 𝕜) u j (a i)) := by
  intro w
  let f : A →ₐ[𝕜] A := (Unitary.conjStarAlgAut 𝕜 A (u ^ j)).toAlgEquiv.toAlgHom
  have hword : (w.map a).prod ∈ B := B.list_prod_mem (fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact ha i)
  have he := expectation_haarConjugate φ u hu B hf j hword
  change φ.expectation (w.map a).prod = φ.expectation (w.map (f ∘ a)).prod
  rw [← List.map_map, ← map_list_prod]
  exact he.symm

/-- For a star-closed original algebra, each entire copy preserves ALL joint
star moments as well as its freely independent placement. -/
theorem sameStarDistribution_haarConjugate (φ : ProbabilitySpace 𝕜 A)
    (u : unitary A) (hu : IsHaarUnitary φ u) (B : StarSubalgebra 𝕜 A)
    (hf : FreelyIndependent φ (haarBasePair u B.toSubalgebra)) (j : ℤ) (a : I → A)
    (ha : ∀ i, a i ∈ B) :
    SameStarDistribution φ φ a (fun i => haarConjugate (𝕜 := 𝕜) u j (a i)) := by
  have he : starFamily (fun i => haarConjugate (𝕜 := 𝕜) u j (a i)) =
      fun x => haarConjugate (𝕜 := 𝕜) u j (starFamily a x) := by
    funext x
    rcases x with ⟨i, b⟩
    cases b
    · rfl
    · change star (Unitary.conjStarAlgAut 𝕜 A (u ^ j) (a i)) =
        Unitary.conjStarAlgAut 𝕜 A (u ^ j) (star (a i))
      exact (map_star (Unitary.conjStarAlgAut 𝕜 A (u ^ j)) (a i)).symm
  unfold SameStarDistribution
  rw [he]
  exact sameDistribution_haarConjugate φ u hu B.toSubalgebra hf j (starFamily a)
    (fun x => by
      rcases x with ⟨i, b⟩
      cases b
      · exact ha i
      · exact B.star_mem' (ha i))
end FreeProbability
