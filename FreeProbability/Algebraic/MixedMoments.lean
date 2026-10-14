import FreeProbability.Algebraic.Freeness
import Mathlib.Tactic.LinearCombination

/-! # Low-order free mixed moments, without a trace assumption -/

namespace FreeProbability.FreelyIndependent

variable {𝕜 A I : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
  {φ : ProbabilitySpace 𝕜 A} {B : I → Subalgebra 𝕜 A}

theorem centered_triple (h : FreelyIndependent φ B) {i j : I} (hij : i ≠ j)
    {a b c : A} (ha : a ∈ B i) (hb : b ∈ B j) (hc : c ∈ B i) :
    φ.expectation (φ.center a * φ.center b * φ.center c) = 0 := by
  simpa [mul_assoc] using
    h [(i, φ.center a), (j, φ.center b), (i, φ.center c)] (by simp)
      (by simp [hij, hij.symm])
      (by simp only [List.mem_cons, List.not_mem_nil, or_false];
          rintro x (rfl | rfl | rfl)
          · exact φ.center_mem _ ha
          · exact φ.center_mem _ hb
          · exact φ.center_mem _ hc)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false];
          rintro x (rfl | rfl | rfl) <;> exact φ.expectation_center _)

/-- A letter from a free second subalgebra can be replaced by its expectation
inside a three-letter word whose outer letters belong to the first subalgebra. -/
theorem expectation_mul_mul (h : FreelyIndependent φ B) {i j : I} (hij : i ≠ j)
    {a b c : A} (ha : a ∈ B i) (hb : b ∈ B j) (hc : c ∈ B i) :
    φ.expectation (a * b * c) = φ.expectation (a * c) * φ.expectation b := by
  have hz := h.centered_triple hij ha hb hc
  have hab := h.expectation_mul hij ha hb
  have hbc := h.expectation_mul hij.symm hb hc
  simp only [ProbabilitySpace.center, sub_mul, mul_sub,
    Algebra.algebraMap_eq_smul_one, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    one_mul, mul_one, map_sub, map_smul, ProbabilitySpace.expectation_one, smul_eq_mul] at hz
  rw [hab, hbc] at hz
  linear_combination hz

theorem centered_quadruple (h : FreelyIndependent φ B) {i j : I} (hij : i ≠ j)
    {a b c d : A} (ha : a ∈ B i) (hb : b ∈ B j) (hc : c ∈ B i) (hd : d ∈ B j) :
    φ.expectation (φ.center a * φ.center b * φ.center c * φ.center d) = 0 := by
  simpa [mul_assoc] using
    h [(i, φ.center a), (j, φ.center b), (i, φ.center c), (j, φ.center d)] (by simp)
      (by simp [hij, hij.symm])
      (by simp only [List.mem_cons, List.not_mem_nil, or_false];
          rintro x (rfl | rfl | rfl | rfl)
          · exact φ.center_mem _ ha
          · exact φ.center_mem _ hb
          · exact φ.center_mem _ hc
          · exact φ.center_mem _ hd)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false];
          rintro x (rfl | rfl | rfl | rfl) <;> exact φ.expectation_center _)

/-- The first nontrivial alternating fourth-moment formula. -/
theorem expectation_four (h : FreelyIndependent φ B) {i j : I} (hij : i ≠ j)
    {a b c d : A} (ha : a ∈ B i) (hb : b ∈ B j) (hc : c ∈ B i) (hd : d ∈ B j) :
    φ.expectation (a * b * c * d) =
      φ.expectation (a * c) * φ.expectation b * φ.expectation d +
      φ.expectation a * φ.expectation c * φ.expectation (b * d) -
      φ.expectation a * φ.expectation b * φ.expectation c * φ.expectation d := by
  have hz := h.centered_quadruple hij ha hb hc hd
  have hab := h.expectation_mul hij ha hb
  have had := h.expectation_mul hij ha hd
  have hbc := h.expectation_mul hij.symm hb hc
  have hcd := h.expectation_mul hij hc hd
  have habc := h.expectation_mul_mul hij ha hb hc
  have hbcd := h.expectation_mul_mul hij.symm hb hc hd
  have habd := h.expectation_mul hij ha ((B j).mul_mem hb hd)
  have hacd := h.expectation_mul hij ((B i).mul_mem ha hc) hd
  simp only [ProbabilitySpace.center, sub_mul, mul_sub,
    Algebra.algebraMap_eq_smul_one, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    one_mul, mul_one, map_sub, map_smul, ProbabilitySpace.expectation_one, smul_eq_mul] at hz
  simp only [← mul_assoc] at habd
  rw [hab, had, hbc, hcd, habc, hbcd, habd, hacd] at hz
  linear_combination hz

/-- The second product moment of free idempotents. No spectral law is asserted. -/
theorem expectation_idempotent_product_sq (h : FreelyIndependent φ B)
    {i j : I} (hij : i ≠ j) {p q : A} (hp : p ∈ B i) (hq : q ∈ B j)
    (hpp : p * p = p) (hqq : q * q = q) :
    φ.expectation ((p * q) ^ 2) =
      φ.expectation p * φ.expectation q *
        (φ.expectation p + φ.expectation q - φ.expectation p * φ.expectation q) := by
  have h4 := h.expectation_four hij hp hq hp hq
  rw [hpp, hqq] at h4
  rw [pow_two, ← mul_assoc, h4]
  ring

end FreeProbability.FreelyIndependent
