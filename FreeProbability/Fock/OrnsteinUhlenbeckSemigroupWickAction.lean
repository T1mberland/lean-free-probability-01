import FreeProbability.Fock.OrnsteinUhlenbeckSemigroupCP

/-! # Actual Wick eigenvectors of the genuine native C-star OU self-map -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable {I H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Genuine recursive Wick polynomial as an element of the literal native C-star algebra. -/
def familyClosedWick (e : I → H) (w : List I) : tensorFamilyAlgebra e :=
  ⟨familyWick e w, (StarAlgebra.adjoin ℂ (Set.range (tensorFamilyField e))).le_topologicalClosure
    (familyWick_mem_polynomial e w)⟩

@[simp] theorem familyClosedWick_nil (e : I → H) : familyClosedWick e [] = 1 := rfl
@[simp] theorem familyClosedWick_singleton (e : I → H) (i : I) :
    familyClosedWick e [i] = tensorFamilyGenerator e i := Subtype.ext (familyWick_singleton e i)

theorem familyClosedWick_cons_cons (e : I → H) (i j : I) (w : List I) :
    familyClosedWick e (i :: j :: w) = tensorFamilyGenerator e i * familyClosedWick e (j :: w) -
      inner ℂ (e i) (e j) • familyClosedWick e w := Subtype.ext (familyWick_cons_cons e i j w)

/-- The genuine C-star embedding sends recursive Wick polynomials to the actual included Wick polynomials. -/
theorem includedFamilyEmbedding_Wick (V : H →ₗᵢ[ℂ] K) (e : I → H) (he : Orthonormal ℂ e) (w : List I) :
    includedFamilyEmbedding V e he (familyClosedWick e w) =
      familyClosedWick (fun i => V (e i)) w := by
  induction w using List.twoStepInduction with
  | nil => rw [familyClosedWick_nil, familyClosedWick_nil, map_one]
  | singleton i => rw [familyClosedWick_singleton, familyClosedWick_singleton, includedFamilyEmbedding_generator]
  | cons_cons i j w hw hjw =>
    let F := includedFamilyEmbedding V e he
    have hs : F (inner ℂ (e i) (e j) • familyClosedWick e w) =
        inner ℂ (e i) (e j) • F (familyClosedWick e w) :=
      map_smul F.toAlgHom _ _
    have hm : F (tensorFamilyGenerator e i * familyClosedWick e (j :: w)) =
        F (tensorFamilyGenerator e i) * F (familyClosedWick e (j :: w)) :=
      map_mul F.toAlgHom _ _
    have hd : F (tensorFamilyGenerator e i * familyClosedWick e (j :: w) -
        inner ℂ (e i) (e j) • familyClosedWick e w) =
        F (tensorFamilyGenerator e i * familyClosedWick e (j :: w)) -
          F (inner ℂ (e i) (e j) • familyClosedWick e w) :=
      map_sub F.toAlgHom _ _
    have hr := familyClosedWick_cons_cons (fun i => V (e i)) i j w
    rw [V.inner_map_map] at hr
    calc
      _ = F (tensorFamilyGenerator e i * familyClosedWick e (j :: w) -
          inner ℂ (e i) (e j) • familyClosedWick e w) :=
        congrArg F (familyClosedWick_cons_cons e i j w)
      _ = F (tensorFamilyGenerator e i) * F (familyClosedWick e (j :: w)) -
          inner ℂ (e i) (e j) • F (familyClosedWick e w) :=
        hd.trans (congrArg₂ (· - ·) hm hs)
      _ = tensorFamilyGenerator (fun i => V (e i)) i *
          familyClosedWick (fun i => V (e i)) (j :: w) -
          inner ℂ (e i) (e j) • familyClosedWick (fun i => V (e i)) w :=
        congrArg₂ (· - ·)
          (congrArg₂ (· * ·) (includedFamilyEmbedding_generator V e he i) (hjw j))
          (congrArg (inner ℂ (e i) (e j) • ·) hw)
      _ = _ := hr.symm


/-- Every true Wick word is an eigenvector of the actual native OU self-map, with exact degree. -/
theorem familyOU_Wick (e : I → H) (he : Orthonormal ℂ e) (r s : ℝ)
    (hrs : r ^ 2 + s ^ 2 = 1) (w : List I) :
    familyOU e he r s hrs (familyClosedWick e w) = (r : ℂ) ^ w.length • familyClosedWick e w := by
  change rotatedIncludedFamilyMap r s hrs e
    (includedFamilyEmbedding (doubledFirst H) e he (familyClosedWick e w)) = _
  rw [includedFamilyEmbedding_Wick]
  apply Subtype.ext
  change rotatedFockCompression H r s hrs (familyWick (fun i => doubledFirst H (e i)) w) =
    (r : ℂ) ^ w.length • familyWick e w
  exact rotatedCompression_included_familyWick r s hrs e w

/-- At nonnegative time the actual degree multiplier is precisely (e⁻ᵗ)ⁿ. -/
theorem familyOUTime_Wick (e : I → H) (he : Orthonormal ℂ e) (t : ℝ) (ht : 0 ≤ t) (w : List I) :
    familyOUTime e he t ht (familyClosedWick e w) =
      (Real.exp (-t) : ℂ) ^ w.length • familyClosedWick e w := familyOU_Wick e he _ _ _ w

end FreeProbability.Fock
