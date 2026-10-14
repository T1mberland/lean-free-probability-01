import FreeProbability.Algebraic.HaarUnitary

/-! # Centered telescoping words for Haar conjugation -/

namespace FreeProbability
variable {𝕜 A : Type*} [Field 𝕜] [StarRing 𝕜] [Ring A] [StarRing A]
  [Algebra 𝕜 A] [StarModule 𝕜 A]

/-- The entire original algebra and the entire generated Haar star algebra. -/
def haarBasePair (u : unitary A) (B : Subalgebra 𝕜 A) : Bool → Subalgebra 𝕜 A :=
  fun b => if b then haarUnitaryAlgebra u else B

/-- Genuine unitary-group conjugation, implemented by the actual star algebra automorphism. -/
def haarConjugate (u : unitary A) (j : ℤ) (a : A) : A :=
  Unitary.conjStarAlgAut 𝕜 A (u ^ j) a

omit [StarRing 𝕜] [StarModule 𝕜 A] in
theorem haarConjugate_eq (u : unitary A) (j : ℤ) (a : A) :
    haarConjugate (𝕜 := 𝕜) u j a = unitaryPower u j * a * unitaryPower u (-j) := by
  simp only [haarConjugate, Unitary.conjStarAlgAut_apply, unitaryPower_neg]
  rfl

/-- Conjugation preserves the restricted expectation by Haar freeness alone;
no cyclicity of the ambient functional is needed. -/
theorem expectation_haarConjugate (φ : ProbabilitySpace 𝕜 A) (u : unitary A)
    (hu : IsHaarUnitary φ u) (B : Subalgebra 𝕜 A)
    (hf : FreelyIndependent φ (haarBasePair u B)) (j : ℤ) {a : A} (ha : a ∈ B) :
    φ.expectation (haarConjugate (𝕜 := 𝕜) u j a) = φ.expectation a := by
  by_cases hj : j = 0
  · simp [hj, haarConjugate]
  have hz := hf [(true, unitaryPower u j), (false, φ.center a), (true, unitaryPower u (-j))]
    (by simp) (by simp)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl)
      · exact unitaryPower_mem_haarUnitaryAlgebra u j
      · exact φ.center_mem B ha
      · exact unitaryPower_mem_haarUnitaryAlgebra u (-j))
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl)
      · exact hu j hj
      · exact φ.expectation_center a
      · exact hu (-j) (neg_ne_zero.mpr hj))
  have hc : φ.expectation (haarConjugate (𝕜 := 𝕜) u j (φ.center a)) = 0 := by
    simpa [haarConjugate_eq, mul_assoc] using hz
  let f : A →ₐ[𝕜] A := (Unitary.conjStarAlgAut 𝕜 A (u ^ j)).toAlgEquiv.toAlgHom
  have he := congrArg f (φ.center_add_expectation a)
  rw [map_add, AlgHom.commutes] at he
  have hev := congrArg φ.expectation he
  rw [map_add, φ.expectation_algebraMap] at hev
  change φ.expectation (haarConjugate (𝕜 := 𝕜) u j (φ.center a)) + φ.expectation a =
    φ.expectation (haarConjugate (𝕜 := 𝕜) u j a) at hev
  rw [hc, zero_add] at hev
  exact hev.symm

/-- Zero peripheral powers are omitted rather than inserted as uncentered letters. -/
def haarPowerLetter (u : unitary A) (j : ℤ) : List (Bool × A) :=
  if j = 0 then [] else [(true, unitaryPower u j)]

@[simp] theorem haarPowerLetter_product (u : unitary A) (j : ℤ) :
    ((haarPowerLetter u j).map Prod.snd).prod = unitaryPower u j := by
  by_cases hj : j = 0 <;> simp [haarPowerLetter, hj]

/-- Interior powers record differences of adjacent conjugation indices. -/
def haarExpandedTail (u : unitary A) (j : ℤ) : List (ℤ × A) → List (Bool × A)
  | [] => haarPowerLetter u (-j)
  | (k, a) :: w => haarPowerLetter u (k - j) ++ [(false, a)] ++ haarExpandedTail u k w

/-- The complete expanded word has possibly omitted peripheral powers. -/
def haarExpandedWord (u : unitary A) : List (ℤ × A) → List (Bool × A)
  | [] => []
  | (j, a) :: w => haarPowerLetter u j ++ [(false, a)] ++ haarExpandedTail u j w

omit [StarRing 𝕜] [StarModule 𝕜 A] in
/-- The expanded tail telescopes using group powers, without ambient inverses. -/
theorem haarExpandedTail_product (u : unitary A) (j : ℤ) (w : List (ℤ × A)) :
    ((haarExpandedTail u j w).map Prod.snd).prod =
      unitaryPower u (-j) * (w.map (fun x => haarConjugate (𝕜 := 𝕜) u x.1 x.2)).prod := by
  induction w generalizing j with
  | nil => simp [haarExpandedTail]
  | cons x w ih =>
    rcases x with ⟨k, a⟩
    simp only [haarExpandedTail, List.map_append, List.prod_append, haarPowerLetter_product,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ih, haarConjugate_eq]
    rw [show k - j = -j + k by omega, unitaryPower_add]
    simp only [mul_assoc]

omit [StarRing 𝕜] [StarModule 𝕜 A] in
/-- The actual product of conjugates equals the actual expanded product. -/
theorem haarExpandedWord_product (u : unitary A) (w : List (ℤ × A)) :
    ((haarExpandedWord u w).map Prod.snd).prod =
      (w.map (fun x => haarConjugate (𝕜 := 𝕜) u x.1 x.2)).prod := by
  cases w with
  | nil => simp [haarExpandedWord]
  | cons x w =>
    rcases x with ⟨j, a⟩
    simp only [haarExpandedWord, List.map_append, List.prod_append, haarPowerLetter_product,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      haarConjugate_eq, mul_assoc]
    rw [haarExpandedTail_product (𝕜 := 𝕜) u j w]
    simp only [haarConjugate_eq, mul_assoc]

/-- The false letter followed by a tail is alternating because original
ADJACENT indices differ. Nonadjacent repeated indices are permitted. -/
theorem haarExpandedTail_isChain (u : unitary A) (j : ℤ) (a : A) (w : List (ℤ × A))
    (hw : ((j, a) :: w).IsChain (fun x y => x.1 ≠ y.1)) :
    ((false, a) :: haarExpandedTail u j w).IsChain (fun x y => x.1 ≠ y.1) := by
  induction w generalizing j a with
  | nil =>
    by_cases hj : -j = 0 <;> simp [haarExpandedTail, haarPowerLetter, hj]
  | cons x w ih =>
    rcases x with ⟨k, b⟩
    have hh : j ≠ k ∧ ((k, b) :: w).IsChain (fun x y => x.1 ≠ y.1) :=
      List.isChain_cons_cons.mp hw
    have hdiff : k - j ≠ 0 := by omega
    simpa only [haarExpandedTail, haarPowerLetter, hdiff, ite_false, List.cons_append,
      List.nil_append, List.isChain_cons_cons, ne_eq, Bool.false_eq_true, not_false_eq_true,
      Bool.true_eq_false, true_and] using ih k b hh.2

/-- The entire expanded word is genuinely alternating. -/
theorem haarExpandedWord_isChain (u : unitary A) (w : List (ℤ × A))
    (hw : w.IsChain (fun x y => x.1 ≠ y.1)) :
    (haarExpandedWord u w).IsChain (fun x y => x.1 ≠ y.1) := by
  cases w with
  | nil => simp [haarExpandedWord]
  | cons x w =>
    rcases x with ⟨j, a⟩
    have ht := haarExpandedTail_isChain u j a w hw
    by_cases hj : j = 0 <;>
      simpa [haarExpandedWord, haarPowerLetter, hj] using ht

/-- Every retained power letter is centered and belongs to the full Haar algebra. -/
theorem haarPowerLetter_valid (φ : ProbabilitySpace 𝕜 A) (u : unitary A)
    (hu : IsHaarUnitary φ u) (B : Subalgebra 𝕜 A) (j : ℤ)
    {x : Bool × A} (hx : x ∈ haarPowerLetter u j) :
    x.2 ∈ haarBasePair u B x.1 ∧ φ.expectation x.2 = 0 := by
  by_cases hj : j = 0
  · simp [haarPowerLetter, hj] at hx
  · have he : x = (true, unitaryPower u j) := by simpa [haarPowerLetter, hj] using hx
    subst x
    exact ⟨unitaryPower_mem_haarUnitaryAlgebra u j, hu j hj⟩

/-- All expanded letters are centered in their corresponding original algebra. -/
theorem haarExpandedTail_valid (φ : ProbabilitySpace 𝕜 A) (u : unitary A)
    (hu : IsHaarUnitary φ u) (B : Subalgebra 𝕜 A) (j : ℤ) (w : List (ℤ × A))
    (hmem : ∀ x ∈ w, x.2 ∈ B) (hzero : ∀ x ∈ w, φ.expectation x.2 = 0) :
    ∀ x ∈ haarExpandedTail u j w,
      x.2 ∈ haarBasePair u B x.1 ∧ φ.expectation x.2 = 0 := by
  induction w generalizing j with
  | nil => exact fun x hx => haarPowerLetter_valid φ u hu B (-j) hx
  | cons y w ih =>
    rcases y with ⟨k, a⟩
    intro x hx
    simp only [haarExpandedTail, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (hx | he) | hx
    · exact haarPowerLetter_valid φ u hu B (k - j) hx
    · subst x
      exact ⟨hmem (k, a) (by simp), hzero (k, a) (by simp)⟩
    · exact ih k (fun y hy => hmem y (by simp [hy])) (fun y hy => hzero y (by simp [hy])) x hx

theorem haarExpandedWord_valid (φ : ProbabilitySpace 𝕜 A) (u : unitary A)
    (hu : IsHaarUnitary φ u) (B : Subalgebra 𝕜 A) (w : List (ℤ × A))
    (hmem : ∀ x ∈ w, x.2 ∈ B) (hzero : ∀ x ∈ w, φ.expectation x.2 = 0) :
    ∀ x ∈ haarExpandedWord u w,
      x.2 ∈ haarBasePair u B x.1 ∧ φ.expectation x.2 = 0 := by
  cases w with
  | nil => simp [haarExpandedWord]
  | cons y w =>
    rcases y with ⟨j, a⟩
    intro x hx
    simp only [haarExpandedWord, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (hx | he) | hx
    · exact haarPowerLetter_valid φ u hu B j hx
    · subst x
      exact ⟨hmem (j, a) (by simp), hzero (j, a) (by simp)⟩
    · exact haarExpandedTail_valid φ u hu B j w
        (fun y hy => hmem y (by simp [hy])) (fun y hy => hzero y (by simp [hy])) x hx

/-- A nonempty original word leaves at least its first base-algebra letter. -/
theorem haarExpandedWord_ne_nil (u : unitary A) {w : List (ℤ × A)} (hw : w ≠ []) :
    haarExpandedWord u w ≠ [] := by
  cases w with
  | nil => exact False.elim (hw rfl)
  | cons y w =>
    rcases y with ⟨j, a⟩
    simp [haarExpandedWord]

/-- Complete alternating products of centered conjugates vanish. The original
indices need only differ ADJACENTLY, so all nonadjacent repetitions are allowed. -/
theorem expectation_haarConjugates_prod_eq_zero (φ : ProbabilitySpace 𝕜 A) (u : unitary A)
    (hu : IsHaarUnitary φ u) (B : Subalgebra 𝕜 A)
    (hf : FreelyIndependent φ (haarBasePair u B)) (w : List (ℤ × A))
    (hw : w ≠ []) (hchain : w.IsChain (fun x y => x.1 ≠ y.1))
    (hmem : ∀ x ∈ w, x.2 ∈ B) (hzero : ∀ x ∈ w, φ.expectation x.2 = 0) :
    φ.expectation (w.map (fun x => haarConjugate (𝕜 := 𝕜) u x.1 x.2)).prod = 0 := by
  rw [← haarExpandedWord_product]
  have hv := haarExpandedWord_valid φ u hu B w hmem hzero
  exact hf (haarExpandedWord u w) (haarExpandedWord_ne_nil u hw)
    (haarExpandedWord_isChain u w hchain) (fun x hx => (hv x hx).1) (fun x hx => (hv x hx).2)
end FreeProbability
