import FreeProbability.RandomMatrix.OrthogonalInvariantVanishing
import Mathlib.Logic.Equiv.Fintype

/-! # Combinatorial induction prerequisites for stable invariant-tensor spanning -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual finite set of colors occurring in a tuple. -/
def tupleColors {k : ℕ} (i : Fin k → n) : Finset n := Finset.univ.image i

private theorem exists_true_of_ne_all_false {X : Type*} (γ : X → Bool)
    (h : γ ≠ (fun _ => false)) : ∃ a, γ a = true := by
  have hn : ¬ ∀ a, γ a = false := fun he => h (funext he)
  obtain ⟨a, ha⟩ := not_forall.mp hn
  cases he : γ a
  · exact False.elim (ha he)
  · exact ⟨a, he⟩

private theorem exists_false_of_ne_all_true {X : Type*} (γ : X → Bool)
    (h : γ ≠ (fun _ => true)) : ∃ a, γ a = false := by
  have hn : ¬ ∀ a, γ a = true := fun he => h (funext he)
  obtain ⟨a, ha⟩ := not_forall.mp hn
  cases he : γ a
  · exact ⟨a, he⟩
  · exact False.elim (ha he)

omit [Fintype n] in
/-- Every proper split retains the old color and adds exactly the fresh color. -/
theorem tupleColors_colorSplitTuple {k : ℕ} (i : Fin k → n) (c d : n)
    (γ : ColorSites i c → Bool) (hfalse : γ ≠ (fun _ => false)) (htrue : γ ≠ (fun _ => true)) :
    tupleColors (colorSplitTuple i c d γ) = insert d (tupleColors i) := by
  obtain ⟨aTrue, hat⟩ := exists_true_of_ne_all_false γ hfalse
  obtain ⟨af, haf⟩ := exists_false_of_ne_all_true γ htrue
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    by_cases hc : i a = c
    · cases hb : γ ⟨a, hc⟩
      · apply Finset.mem_insert_of_mem
        exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, by simp [colorSplitTuple, hc, hb]⟩
      · simp [colorSplitTuple, hc, hb]
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, by simp [colorSplitTuple, hc]⟩
  · intro hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_image.mpr ⟨aTrue.1, Finset.mem_univ _, by simp [colorSplitTuple, aTrue.2, hat]⟩
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      by_cases hc : i a = c
      · exact Finset.mem_image.mpr ⟨af.1, Finset.mem_univ _, by simp [colorSplitTuple, af.2, haf, hc]⟩
      · exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, by simp [colorSplitTuple, hc]⟩

omit [Fintype n] in
/-- Fresh-color proper splitting increases the actual number of used colors
by exactly one, supplying the strict induction direction. -/
theorem card_tupleColors_colorSplitTuple {k : ℕ} (i : Fin k → n) (c d : n)
    (hfresh : ∀ a, i a ≠ d) (γ : ColorSites i c → Bool)
    (hfalse : γ ≠ (fun _ => false)) (htrue : γ ≠ (fun _ => true)) :
    (tupleColors (colorSplitTuple i c d γ)).card = (tupleColors i).card + 1 := by
  rw [tupleColors_colorSplitTuple i c d γ hfalse htrue]
  apply Finset.card_insert_of_notMem
  intro hd
  obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hd
  exact hfresh a he

omit [Fintype n] in
/-- Any actual tuple with every used color appearing twice is a genuinely
colored ordinary pairing tuple, with an injective pair-color assignment. -/
theorem exists_pairingTuple_of_color_counts_two {r : ℕ} (i : Fin (2 * r) → n)
    (hcounts : ∀ c ∈ tupleColors i, (Finset.univ.filter (fun a => i a = c)).card = 2) :
    ∃ (e : PairingSites r) (b : Fin r ↪ n), i = pairingTuple e b := by
  let S := Set.range i
  let : Fintype S := Fintype.ofFinite S
  let f : Fin (2 * r) → S := fun a => ⟨i a, ⟨a, rfl⟩⟩
  have hfiber (x : S) : Fintype.card {a : Fin (2 * r) // f a = x} = 2 := by
    let eFiber := Equiv.subtypeEquivRight (fun a : Fin (2 * r) =>
      show f a = x ↔ i a = x.1 from Subtype.ext_iff)
    rw [Fintype.card_congr eFiber, Fintype.card_subtype]
    exact hcounts x.1 (by obtain ⟨a, ha⟩ := x.2; exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩)
  have hS : Fintype.card S = r := by
    have hc := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
    simp only [Fintype.card_sigma, hfiber, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, Fintype.card_fin] at hc
    omega
  let eS : S ≃ Fin r := Fintype.equivFinOfCardEq hS
  let eF (x : S) : {a : Fin (2 * r) // f a = x} ≃ Fin 2 := Fintype.equivFinOfCardEq (hfiber x)
  let e : PairingSites r := (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight eF).trans ((Equiv.sigmaEquivProd S (Fin 2)).trans
      (Equiv.prodCongr eS (Equiv.refl (Fin 2)))))
  let b : Fin r ↪ n :=
    { toFun := fun a => (eS.symm a).1
      inj' := fun a c he => eS.symm.injective (Subtype.ext he) }
  refine ⟨e, b, ?_⟩
  funext a
  change i a = (eS.symm (eS (f a))).1
  simp only [Equiv.symm_apply_apply]
  rfl

omit [Fintype n] in
private theorem sum_color_counts {k : ℕ} (i : Fin k → n) :
    (∑ c ∈ tupleColors i, (Finset.univ.filter (fun a => i a = c)).card) = k := by
  have h := Finset.card_eq_sum_card_fiberwise
    (f := i) (s := Finset.univ) (t := tupleColors i)
    (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  simpa only [Finset.card_univ, Fintype.card_fin] using h.symm

omit [Fintype n] in
private theorem color_count_pos {k : ℕ} (i : Fin k → n) {c : n} (hc : c ∈ tupleColors i) :
    0 < (Finset.univ.filter (fun a => i a = c)).card := by
  obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hc
  exact Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, he⟩⟩

/-- Even-color tuples with a block larger than a pair genuinely use fewer
than r colors, so stable dimension supplies a fresh color. -/
theorem exists_large_block_and_fresh_color {r : ℕ} (i : Fin (2 * r) → n)
    (hr : r ≤ Fintype.card n)
    (heven : ∀ c ∈ tupleColors i, Even (Finset.univ.filter (fun a => i a = c)).card)
    (hpair : ¬ ∀ c ∈ tupleColors i, (Finset.univ.filter (fun a => i a = c)).card = 2) :
    ∃ c d : n, c ≠ d ∧ (∀ a, i a ≠ d) ∧
      4 ≤ (Finset.univ.filter (fun a => i a = c)).card ∧ (tupleColors i).card < r := by
  have htwo (c : n) (hc : c ∈ tupleColors i) : 2 ≤ (Finset.univ.filter (fun a => i a = c)).card := by
    have hp := color_count_pos i hc
    obtain ⟨m, hm⟩ := heven c hc
    omega
  obtain ⟨c, hc, hcount⟩ : ∃ c ∈ tupleColors i, (Finset.univ.filter (fun a => i a = c)).card ≠ 2 := by
    simpa only [not_forall, exists_prop] using hpair
  have hfour : 4 ≤ (Finset.univ.filter (fun a => i a = c)).card := by
    have hp := color_count_pos i hc
    obtain ⟨m, hm⟩ := heven c hc
    omega
  have hsum := Finset.sum_lt_sum htwo ⟨c, hc, by omega⟩
  rw [sum_color_counts] at hsum
  simp only [Finset.sum_const, smul_eq_mul] at hsum
  have hcard : (tupleColors i).card < r := by omega
  have hex : ∃ d : n, d ∉ tupleColors i := by
    by_contra hn
    have hall : ∀ d : n, d ∈ tupleColors i := by simpa only [not_exists, not_not] using hn
    have heq : tupleColors i = Finset.univ := Finset.ext (fun d => by simp [hall d])
    rw [heq, Finset.card_univ] at hcard
    omega
  obtain ⟨d, hd⟩ := hex
  have hfresh : ∀ a, i a ≠ d := fun a he => hd (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, he⟩)
  have hcd : c ≠ d := fun he => hd (he ▸ hc)
  exact ⟨c, d, hcd, hfresh, hfour, hcard⟩

/-- In stable dimension, genuine invariant tensors are determined by all
injectively colored pair-block coefficients. This is a zero-evaluation theorem,
with scalar rotation relations entirely derived rather than assumed. -/
theorem invariantTensor_eq_zero_of_pair_tuple_coefficients {r : ℕ}
    (hr : r ≤ Fintype.card n) (v : EuclideanSpace ℝ (Fin (2 * r) → n))
    (hv : v ∈ (tensorPowerRepresentation (n := n) (2 * r)).fixedVectors)
    (hbase : ∀ (e : PairingSites r) (b : Fin r ↪ n), v (pairingTuple e b) = 0) : v = 0 := by
  have hall : ∀ m : ℕ, ∀ i : Fin (2 * r) → n, r - (tupleColors i).card = m → v i = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro i hi
      by_cases hodd : ∃ c ∈ tupleColors i, Odd (Finset.univ.filter (fun a => i a = c)).card
      · obtain ⟨c, hc, hco⟩ := hodd
        exact invariantTensor_coefficient_eq_zero_of_odd_count v hv i c hco
      have heven : ∀ c ∈ tupleColors i, Even (Finset.univ.filter (fun a => i a = c)).card := by
        intro c hc
        exact (Nat.even_or_odd _).resolve_right (fun hco => hodd ⟨c, hc, hco⟩)
      by_cases hpair : ∀ c ∈ tupleColors i, (Finset.univ.filter (fun a => i a = c)).card = 2
      · obtain ⟨e, b, he⟩ := exists_pairingTuple_of_color_counts_two i hpair
        rw [he]
        exact hbase e b
      obtain ⟨c, d, hcd, hfresh, hm, hcard⟩ := exists_large_block_and_fresh_color i hr heven hpair
      apply invariantTensor_coefficient_eq_zero_of_proper_splits v hv i c d hcd hfresh hm
      intro γ hfalse htrue
      have hsplit := card_tupleColors_colorSplitTuple i c d hfresh γ hfalse htrue
      apply ih (r - (tupleColors (colorSplitTuple i c d γ)).card) (by omega)
        (colorSplitTuple i c d γ) rfl
  apply PiLp.ext
  intro i
  exact hall _ i rfl

/-- Genuine invariant coefficients depend only on the tuple equality pattern,
proved by extending the two injective quotient-color maps to a permutation. -/
theorem invariantTensor_coefficient_eq_of_ker_eq {k : ℕ}
    (v : EuclideanSpace ℝ (Fin k → n))
    (hv : v ∈ (tensorPowerRepresentation (n := n) k).fixedVectors)
    (i j : Fin k → n) (hker : Setoid.ker i = Setoid.ker j) : v i = v j := by
  let f : Quotient (Setoid.ker i) → n := Setoid.kerLift i
  let g : Quotient (Setoid.ker i) → n := Quotient.lift j (fun a b h => by
    change (Setoid.ker j).r a b
    rw [← hker]
    exact h)
  have hg : Function.Injective g := by
    intro x y hxy
    induction x using Quotient.inductionOn with
    | h a =>
      induction y using Quotient.inductionOn with
      | h b =>
        apply Quotient.sound
        have hj : (Setoid.ker j).r a b := hxy
        rw [← hker] at hj
        exact hj
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g (Setoid.kerLift_injective i) hg
  have he : (fun a => σ (i a)) = j := funext (fun a => hσ (Quotient.mk _ a))
  have h := invariantTensor_permutation v hv i σ
  rw [he] at h
  exact h.symm

omit [Fintype n] [DecidableEq n] in
private theorem ker_pairingTuple {r : ℕ} (e : PairingSites r) (b : Fin r ↪ n) :
    Setoid.ker (pairingTuple e b) = pairingSetoid e := by
  ext a c
  exact b.injective.eq_iff

/-- Exact isolating coefficients for ANY tuple with the selected intrinsic
pairing equality pattern, independent of its actual coordinate labels. -/
theorem ordinaryPairingTensor_coefficient_of_ker_eq {r : ℕ} (p q : OrdinaryPairing r)
    (i : Fin (2 * r) → n) (hi : Setoid.ker i = pairingSetoid p.out) :
    (ordinaryPairingTensor (n := n) q) i = if q = p then (1 : ℝ) else 0 := by
  let b : Fin r ↪ n :=
    { toFun := fun a => i (p.out.symm (a, 0))
      inj' := by
        intro a c he
        have hr : (Setoid.ker i).r (p.out.symm (a, 0)) (p.out.symm (c, 0)) := he
        rw [hi] at hr
        change (p.out (p.out.symm (a, 0))).1 = (p.out (p.out.symm (c, 0))).1 at hr
        simpa only [Equiv.apply_symm_apply] using hr }
  have he : pairingTuple p.out b = i := by
    funext a
    apply (show pairingSetoid p.out ≤ Setoid.ker i from le_of_eq hi.symm)
    change (p.out (p.out.symm ((p.out a).1, 0))).1 = (p.out a).1
    simp only [Equiv.apply_symm_apply]
  rw [← he]
  exact ordinaryPairingTensor_isolating_coefficient b p q

/-- Every ACTUAL invariant tensor in stable dimension belongs to the genuine
span of ALL ordinary pairing vectors. No spanning premise is assumed. -/
theorem invariantTensor_mem_span_pairings {r : ℕ} (hr : r ≤ Fintype.card n)
    (v : EuclideanSpace ℝ (Fin (2 * r) → n))
    (hv : v ∈ (tensorPowerRepresentation (n := n) (2 * r)).fixedVectors) :
    v ∈ Submodule.span ℝ (Set.range (ordinaryPairingTensor (n := n) (r := r))) := by
  obtain ⟨b : Fin r ↪ n⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin r) ≤ Fintype.card n by simpa using hr)
  let c : OrdinaryPairing r → ℝ := fun p => v (pairingTuple p.out b)
  let w : EuclideanSpace ℝ (Fin (2 * r) → n) := ∑ p : OrdinaryPairing r, c p • ordinaryPairingTensor p
  have hw : w ∈ (tensorPowerRepresentation (n := n) (2 * r)).fixedVectors := by
    apply Submodule.sum_mem
    intro p hp
    exact Submodule.smul_mem _ _ (pairingTensor_mem_fixedVectors p.out)
  have hbase (e : PairingSites r) (b' : Fin r ↪ n) : (v - w) (pairingTuple e b') = 0 := by
    let p : OrdinaryPairing r := Quotient.mk _ e
    have hp : pairingSetoid p.out = pairingSetoid e := Quotient.exact (Quotient.out_eq p)
    have hi : Setoid.ker (pairingTuple e b') = pairingSetoid p.out := by
      rw [ker_pairingTuple, hp]
    have hvp : v (pairingTuple e b') = c p :=
      invariantTensor_coefficient_eq_of_ker_eq v hv _ _ (hi.trans (ker_pairingTuple p.out b).symm)
    have hwp : w (pairingTuple e b') = c p := by
      have he := map_sum (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (2 * r) → n => ℝ) (pairingTuple e b'))
        (fun q : OrdinaryPairing r => c q • ordinaryPairingTensor q) Finset.univ
      change w (pairingTuple e b') = ∑ q : OrdinaryPairing r, c q * (ordinaryPairingTensor q) (pairingTuple e b') at he
      rw [he]
      simp only [ordinaryPairingTensor_coefficient_of_ker_eq p _ _ hi]
      simp
    change v (pairingTuple e b') - w (pairingTuple e b') = 0
    rw [hvp, hwp, sub_self]
  have hz := invariantTensor_eq_zero_of_pair_tuple_coefficients hr (v - w)
    ((tensorPowerRepresentation (n := n) (2 * r)).fixedVectors.sub_mem hv hw) hbase
  have hvw : v = w := sub_eq_zero.mp hz
  rw [hvw]
  apply Submodule.sum_mem
  intro p hp
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

/-- The genuine stable-dimension orthogonal first fundamental theorem:
ALL invariant tensors are exactly the span of ordinary pairing tensors. -/
theorem span_pairingTensors_eq_fixedVectors (r : ℕ) (hr : r ≤ Fintype.card n) :
    Submodule.span ℝ (Set.range (ordinaryPairingTensor (n := n) (r := r))) =
      (tensorPowerRepresentation (n := n) (2 * r)).fixedVectors := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨p, rfl⟩
    exact pairingTensor_mem_fixedVectors p.out
  · exact fun v hv => invariantTensor_mem_span_pairings hr v hv
end FreeProbability.Orthogonal
