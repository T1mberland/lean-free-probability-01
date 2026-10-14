import FreeProbability.Fock.WordIntegrationByParts
import FreeProbability.Combinatorics.NoncrossingPairingWeights

/-!
# The joint free Wick formula for the concrete Fock operators

The operator-derived moment recursion agrees with the independently proved
first-partner recursion on actual noncrossing pairings. Each pair contributes
the Kronecker covariance of its endpoint colors.
-/

noncomputable section
open scoped Classical BigOperators
open FreeProbability.NoncrossingPairing

namespace FreeProbability.Fock

variable {I : Type*} {n : ℕ}

/-- The interior color word in first-partner splitting is exactly the corresponding list prefix. -/
theorem take_tail_ofFn (a : Fin (n + 2) → I) (k : Fin (n + 1)) :
    (List.ofFn (fun b : Fin (n + 1) => a b.succ)).take k.val =
      List.ofFn (fun b : Fin k.val => a (insideEmbedding k b)) := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_ofFn]
    exact Nat.min_eq_left (Nat.le_of_lt k.isLt)
  · intro j hj₁ hj₂
    simp only [List.getElem_take, List.getElem_ofFn]
    apply congrArg a
    apply Fin.ext
    rfl

/-- The exterior color word is the suffix after the matched endpoint. -/
theorem drop_tail_ofFn (a : Fin (n + 2) → I) (k : Fin (n + 1)) :
    (List.ofFn (fun b : Fin (n + 1) => a b.succ)).drop (k.val + 1) =
      List.ofFn (fun b : Fin (n - k.val) => a (outsideEmbedding k b)) := by
  apply List.ext_getElem
  · simp only [List.length_drop, List.length_ofFn]
    omega
  · intro j hj₁ hj₂
    simp only [List.getElem_drop, List.getElem_ofFn]
    apply congrArg a
    apply Fin.ext
    simp only [Fin.val_succ, outsideEmbedding_val]
    omega

/-- The all-order joint moment is the sum of actual noncrossing pairing weights. -/
theorem vacuumExpectation_ofFn_eq_pairingSum (n : ℕ) (a : Fin n → I) :
    vacuumExpectation (operatorWord (List.ofFn a)) =
      pairingSum (fun p q => if a p = a q then (1 : ℂ) else 0) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      cases n with
      | zero => simp [List.ofFn_succ]
      | succ n =>
        rw [pairingSum_succ_succ, List.ofFn_succ, vacuumExpectation_operatorWord_cons]
        apply Fintype.sum_equiv (finCongr (List.length_ofFn (f := fun b : Fin (n + 1) => a b.succ)))
        intro k
        let k' : Fin (n + 1) := finCongr (List.length_ofFn (f := fun b : Fin (n + 1) => a b.succ)) k
        have hk : k'.val = k.val := rfl
        simp only [List.get_eq_getElem, List.getElem_ofFn]
        have he : (⟨k.val, by simpa only [List.length_ofFn] using k.isLt⟩ : Fin (n + 1)).succ = splitPartner k' := by
          apply Fin.ext
          change k.val + 1 = k'.val + 1
          rw [hk]
        simp only [he]
        have ht := take_tail_ofFn a k'
        have hd := drop_tail_ofFn a k'
        have ht' : List.take k.val (List.ofFn (fun b : Fin (n + 1) => a b.succ)) =
            List.ofFn (fun b : Fin k'.val => a (insideEmbedding k' b)) := ht
        have hd' : List.drop (k.val + 1) (List.ofFn (fun b : Fin (n + 1) => a b.succ)) =
            List.ofFn (fun b : Fin (n - k'.val) => a (outsideEmbedding k' b)) := hd
        rw [ht', hd']
        have hki : k'.val < n + 2 := by have := k'.isLt; omega
        have hko : n - k'.val < n + 2 := by omega
        rw [ih k'.val hki, ih (n - k'.val) hko]
        by_cases h : a 0 = a (splitPartner k') <;> simp [h, k']

/-- Literal free Wick formula, with one covariance factor for each actual two-point block. -/
theorem joint_free_wick (n : ℕ) (a : Fin n → I) :
    vacuumExpectation (operatorWord (List.ofFn a)) =
      ∑ p : NoncrossingPairing n, ∏ e ∈ pairingPairs p,
        if a e.1 = a e.2 then (1 : ℂ) else 0 := by
  rw [vacuumExpectation_ofFn_eq_pairingSum]
  unfold pairingSum
  apply Finset.sum_congr rfl
  intro p hp
  exact pairingWeight_eq_prod_pairs p _

/-- The same joint Wick formula for an ordinary finite list of colors. -/
theorem joint_free_wick_list (w : List I) :
    vacuumExpectation (operatorWord w) =
      ∑ p : NoncrossingPairing w.length, ∏ e ∈ pairingPairs p,
        if w.get e.1 = w.get e.2 then (1 : ℂ) else 0 := by
  simpa only [List.ofFn_get] using joint_free_wick w.length w.get

/-- Odd joint moments vanish because actual odd-size pairings do not exist. -/
theorem vacuumExpectation_ofFn_eq_zero_of_odd (n : ℕ) (hn : Odd n) (a : Fin n → I) :
    vacuumExpectation (operatorWord (List.ofFn a)) = 0 := by
  rw [joint_free_wick]
  let : IsEmpty (NoncrossingPairing n) := ⟨fun p => not_nonempty_of_odd hn ⟨p⟩⟩
  simp

/-- The moment of one generator equals the number of actual noncrossing pairings.
The identification of the even count with Catalan numbers is a separate combinatorial theorem. -/
theorem vacuumExpectation_semicircular_pow_eq_pairingCard (i : I) (n : ℕ) :
    vacuumExpectation (semicircular i ^ n) = (Fintype.card (NoncrossingPairing n) : ℂ) := by
  simpa [operatorWord] using joint_free_wick n (fun _ : Fin n => i)

/-- Joint Wick moments in the actual faithful tracial generated C-star algebra. -/
theorem closedGeneratedVacuumState_joint_free_wick (n : ℕ) (a : Fin n → I) :
    (closedGeneratedVacuumState I).expectation
      (List.ofFn (fun k => closedSemicircular (a k))).prod =
      ∑ p : NoncrossingPairing n, ∏ e ∈ pairingPairs p,
        if a e.1 = a e.2 then (1 : ℂ) else 0 := by
  change vacuumExpectation ((closedSemicircularAlgebra I).val
    (List.ofFn (fun k => closedSemicircular (a k))).prod) = _
  rw [map_list_prod, List.map_ofFn]
  change vacuumExpectation (List.ofFn (fun k => semicircular (a k))).prod = _
  simpa only [operatorWord, List.map_ofFn, Function.comp_def] using joint_free_wick n a

end FreeProbability.Fock

