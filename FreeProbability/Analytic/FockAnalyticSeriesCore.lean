import FreeProbability.Fock.WordIntegrationByParts
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Actual norm-convergent analytic series and ordered commutators

Value and derivative series have explicit absolute norm bounds. All series are
actual Banach-algebra sums, and the insertion derivative retains operator order.
-/

noncomputable section
open scoped Classical

namespace FreeProbability

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

/-- The actual continuous linear commutator map in a complex Banach algebra. -/
def analyticCommutator (C : A) : A →L[ℂ] A :=
  ContinuousLinearMap.mul ℂ A C - (ContinuousLinearMap.mul ℂ A).flip C

omit [CompleteSpace A] [NormOneClass A] in
@[simp] theorem analyticCommutator_apply (C X : A) : analyticCommutator C X = C * X - X * C := rfl

/-- The ordered derivative of a power inserts `K` at every possible position. -/
def analyticPowerInsertion (X K : A) (n : ℕ) : A :=
  ∑ k : Fin (n + 1), X ^ k.val * K * X ^ (n - k.val)

omit [CompleteSpace A] [NormOneClass A] in
/-- Exact algebraic power derivative, with no commutativity assumption. -/
theorem analyticCommutator_pow (C X : A) (n : ℕ) :
    analyticCommutator C (X ^ (n + 1)) = analyticPowerInsertion X (analyticCommutator C X) n := by
  have h := commutator_list_prod C (List.replicate (n + 1) X)
  simp only [List.prod_replicate] at h
  rw [analyticCommutator_apply]
  rw [h]
  unfold analyticPowerInsertion
  apply Fintype.sum_equiv (finCongr ((show (List.replicate (n + 1) X).length = n + 1 from List.length_replicate)))
  intro k
  have hk : (finCongr ((show (List.replicate (n + 1) X).length = n + 1 from List.length_replicate)) k).val = k.val := rfl
  simp only [hk]
  have hkn : k.val ≤ n := by omega
  simp only [List.take_replicate, List.drop_replicate, List.prod_replicate,
    List.get_eq_getElem, List.getElem_replicate]
  rw [min_eq_left (by omega : k.val ≤ n + 1)]
  have he : n + 1 - (k.val + 1) = n - k.val := by omega
  rw [he]
  rfl

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
/-- The explicit norm bound controls all `n+1` ordered derivative insertions. -/
theorem norm_analyticPowerInsertion_le (X K : A) (n : ℕ) :
    ‖analyticPowerInsertion X K n‖ ≤ (n + 1 : ℝ) * ‖X‖ ^ n * ‖K‖ := by
  apply (norm_sum_le _ _).trans
  have hb (k : Fin (n + 1)) :
      ‖X ^ k.val * K * X ^ (n - k.val)‖ ≤ ‖X‖ ^ n * ‖K‖ := by
    calc
      _ ≤ (‖X‖ ^ k.val * ‖K‖) * ‖X‖ ^ (n - k.val) :=
        (norm_mul_le _ _).trans (mul_le_mul
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_pow_le X _) (norm_nonneg K)))
          (norm_pow_le X _) (norm_nonneg _) (mul_nonneg (pow_nonneg (norm_nonneg X) _) (norm_nonneg K)))
      _ = ‖X‖ ^ n * ‖K‖ := by
        rw [mul_right_comm, ← pow_add]
        congr 1
        congr 1
        omega
  apply (Finset.sum_le_sum (fun k _ => hb k)).trans
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one]
  exact le_of_eq (by ring)

/-- Actual norm-convergent evaluation of the scalar power series in a bounded algebra element. -/
def analyticSeries (c : ℕ → ℂ) (X : A) : A := ∑' n, c n • X ^ n

/-- The explicit value bound guarantees norm convergence of the actual operator series. -/
theorem summable_analyticSeries (c : ℕ → ℂ) (X : A)
    (hv : Summable (fun n => ‖c n‖ * ‖X‖ ^ n)) : Summable (fun n => c n • X ^ n) :=
  hv.of_norm_bounded (fun n => by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_pow_le X n) (norm_nonneg _))

/-- The explicit derivative bound guarantees norm convergence of the ordered insertion series. -/
theorem summable_analyticInsertionSeries (c : ℕ → ℂ) (X K : A)
    (hd : Summable (fun n : ℕ => (n + 1 : ℝ) * ‖c (n + 1)‖ * ‖X‖ ^ n)) :
    Summable (fun n => c (n + 1) • analyticPowerInsertion X K n) := by
  apply (hd.mul_right ‖K‖).of_norm_bounded
  intro n
  rw [norm_smul]
  calc
    _ ≤ ‖c (n + 1)‖ * ((n + 1 : ℝ) * ‖X‖ ^ n * ‖K‖) :=
      mul_le_mul_of_nonneg_left (norm_analyticPowerInsertion_le X K n) (norm_nonneg _)
    _ = _ := by ring

/-- The commutator of the actual norm-convergent series is the actual convergent derivative series. -/
theorem analyticSeries_commutator (c : ℕ → ℂ) (C X : A)
    (hv : Summable (fun n => ‖c n‖ * ‖X‖ ^ n)) :
    analyticCommutator C (analyticSeries c X) =
      ∑' n, c (n + 1) • analyticPowerInsertion X (analyticCommutator C X) n := by
  rw [analyticSeries, (analyticCommutator C).map_tsum (summable_analyticSeries c X hv)]
  have hs := (analyticCommutator C).summable (summable_analyticSeries c X hv)
  rw [hs.tsum_eq_zero_add]
  simp only [pow_zero, analyticCommutator_apply, map_smul, mul_one, one_mul, sub_self, smul_zero,
    zero_add]
  simp_rw [← analyticCommutator_apply, analyticCommutator_pow]

/-- Both explicit bounds give a convergent derivative series and its exact actual commutator. -/
theorem analyticSeries_commutator_of_norm_bounds (c : ℕ → ℂ) (C X : A)
    (hv : Summable (fun n => ‖c n‖ * ‖X‖ ^ n))
    (hd : Summable (fun n : ℕ => (n + 1 : ℝ) * ‖c (n + 1)‖ * ‖X‖ ^ n)) :
    Summable (fun n => c (n + 1) • analyticPowerInsertion X (analyticCommutator C X) n) ∧
      analyticCommutator C (analyticSeries c X) =
        ∑' n, c (n + 1) • analyticPowerInsertion X (analyticCommutator C X) n :=
  ⟨summable_analyticInsertionSeries c X (analyticCommutator C X) hd,
    analyticSeries_commutator c C X hv⟩

end FreeProbability
