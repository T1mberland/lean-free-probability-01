import FreeProbability.Combinatorics.PartitionMultilinear

/-! # Multilinearity of the recursively constructed free cumulants -/

namespace FreeProbability

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

/-- Ordered joint moments as bundled multilinear maps. -/
def momentMultilinear (φ : ProbabilitySpace 𝕜 A) (n : ℕ) :
    MultilinearMap 𝕜 (fun _ : Fin n => A) 𝕜 :=
  φ.expectation.compMultilinearMap (MultilinearMap.mkPiAlgebraFin 𝕜 n A)

@[simp] theorem momentMultilinear_apply (φ : ProbabilitySpace 𝕜 A) (n : ℕ) (x : Fin n → A) :
    momentMultilinear φ n x = φ.expectation (List.ofFn x).prod := rfl

/-- Construct the cumulant maps in the space of multilinear maps itself. -/
noncomputable def cumulantMultilinear (φ : ProbabilitySpace 𝕜 A) (n : ℕ) :
    MultilinearMap 𝕜 (fun _ : Fin n => A) 𝕜 :=
  if n = 0 then 0 else momentMultilinear φ n -
    ∑ p : ProperNoncrossingPartition n,
      partitionMultilinear p.val (fun s => cumulantMultilinear φ s.val.card)
termination_by n
decreasing_by
  exact p.val.block_card_lt_of_ne_indiscrete p.property s.property

@[simp] theorem cumulantMultilinear_zero (φ : ProbabilitySpace 𝕜 A) :
    cumulantMultilinear φ 0 = 0 := by rw [cumulantMultilinear]; simp

theorem cumulantMultilinear_recursion (φ : ProbabilitySpace 𝕜 A) (n : ℕ) (hn : n ≠ 0) :
    cumulantMultilinear φ n = momentMultilinear φ n -
      ∑ p : ProperNoncrossingPartition n,
        partitionMultilinear p.val (fun s => cumulantMultilinear φ s.val.card) := by
  rw [cumulantMultilinear]
  simp only [hn, ↓reduceIte]

omit [Ring A] in
theorem blockWord_eq_ofFn (w : List A) (s : Finset (Fin w.length)) :
    blockWord w s = List.ofFn (w.get ∘ s.orderEmbOfFin rfl) := by
  rw [List.ofFn_eq_map, ← List.map_map, Finset.listMap_orderEmbOfFin_finRange]
  rfl

omit [Field 𝕜] [Ring A] in
theorem apply_ofFn_get (F : ∀ n, (Fin n → A) → 𝕜) {n : ℕ} (x : Fin n → A) :
    F (List.ofFn x).length (List.ofFn x).get = F n x :=
  congrArg (fun p : Σ n, Fin n → A => F p.1 p.2)
    (List.equivSigmaTuple.apply_symm_apply ⟨n, x⟩)

/-- The bundled construction agrees with the previously constructed free cumulants. -/
theorem cumulantMultilinear_eq (φ : ProbabilitySpace 𝕜 A) (w : List A) :
    cumulantMultilinear φ w.length w.get = cumulant φ w := by
  suffices ∀ n (w : List A), w.length = n →
      cumulantMultilinear φ w.length w.get = cumulant φ w from this w.length w rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hw
    by_cases hnil : w = []
    · subst w
      simp [cumulant]
    have hn : w.length ≠ 0 := fun h => hnil (List.eq_nil_of_length_eq_zero h)
    rw [cumulantMultilinear_recursion φ _ hn]
    simp only [sub_apply, sum_apply, momentMultilinear_apply,
      List.ofFn_get]
    unfold cumulant
    rw [freeCumulant_recursion _ w hnil]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    simp only [partitionMultilinear_apply, blockProduct, partitionContribution]
    apply Finset.prod_congr rfl
    intro s _
    have hlen : s.val.card < n := by
      rw [← hw]
      exact p.val.block_card_lt_of_ne_indiscrete p.property s.property
    have hb := ih s.val.card hlen (blockWord w s.val) (blockWord_length _ _)
    rw [blockWord_eq_ofFn] at hb
    rw [apply_ofFn_get (fun n x => cumulantMultilinear φ n x)
      (w.get ∘ s.val.orderEmbOfFin rfl)] at hb
    simpa only [cumulant, blockWord_eq_ofFn] using hb

theorem cumulant_ofFn (φ : ProbabilitySpace 𝕜 A) {n : ℕ} (x : Fin n → A) :
    cumulant φ (List.ofFn x) = cumulantMultilinear φ n x := by
  rw [← cumulantMultilinear_eq φ (List.ofFn x)]
  exact apply_ofFn_get (fun n x => cumulantMultilinear φ n x) x

/-- Free cumulants are additive in each coordinate, at every order. -/
theorem cumulant_update_add (φ : ProbabilitySpace 𝕜 A) {n : ℕ}
    (x : Fin n → A) (i : Fin n) (a b : A) :
    cumulant φ (List.ofFn (Function.update x i (a + b))) =
      cumulant φ (List.ofFn (Function.update x i a)) +
        cumulant φ (List.ofFn (Function.update x i b)) := by
  simp only [cumulant_ofFn]
  exact (cumulantMultilinear φ n).map_update_add x i a b

/-- Free cumulants are homogeneous in each coordinate, at every order. -/
theorem cumulant_update_smul (φ : ProbabilitySpace 𝕜 A) {n : ℕ}
    (x : Fin n → A) (i : Fin n) (c : 𝕜) (a : A) :
    cumulant φ (List.ofFn (Function.update x i (c • a))) =
      c * cumulant φ (List.ofFn (Function.update x i a)) := by
  simp only [cumulant_ofFn]
  exact (cumulantMultilinear φ n).map_update_smul x i c a

end FreeProbability
