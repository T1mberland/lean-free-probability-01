import FreeProbability.RandomMatrix.OrthogonalColoredTraceCenter

/-! # Genuine finite ordered-product perturbation bounds -/

noncomputable section
open scoped Classical Topology
namespace FreeProbability.Orthogonal
open Matrix Filter
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Actual ordered products have the uniform operator bound, including degree
zero and zero matrix dimension. -/
theorem orderedProduct_Euclidean_opNorm_le {r : ℕ} (K : ℝ) (hK : 0 ≤ K)
    (A : Fin r → Matrix n n ℂ)
    (hA : ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖ ≤ K) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (List.ofFn A).prod‖ ≤ K ^ r := by
  induction r with
  | zero => simpa only [List.ofFn_zero, List.prod_nil, pow_zero] using (Euclidean_opNorm_one_le (n := n))
  | succ r ih =>
    rw [List.ofFn_succ, List.prod_cons, map_mul, pow_succ']
    apply (norm_mul_le _ _).trans
    exact mul_le_mul (hA 0) (ih (fun k => A k.succ) (fun k => hA k.succ)) (norm_nonneg _) (by positivity)

/-- A genuine finite ordered-product difference estimate with every factor
used in its original order; the target is a literal Euclidean operator norm. -/
theorem orderedProduct_Euclidean_opNorm_sub_le {r : ℕ} (K : ℝ) (hK : 0 ≤ K)
    (A B : Fin r → Matrix n n ℂ)
    (hA : ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖ ≤ K)
    (hB : ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖ ≤ K) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) ((List.ofFn A).prod - (List.ofFn B).prod)‖ ≤
      (K + 1) ^ r * ∑ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k - B k)‖ := by
  induction r with
  | zero => simp
  | succ r ih =>
    let AT := (List.ofFn (fun k : Fin r => A k.succ)).prod
    let BT := (List.ofFn (fun k : Fin r => B k.succ)).prod
    have he : A 0 * AT - B 0 * BT = A 0 * (AT - BT) + (A 0 - B 0) * BT := by noncomm_ring
    have hAt : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (AT - BT)‖ ≤
        (K + 1) ^ r * ∑ k : Fin r, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k.succ - B k.succ)‖ :=
      ih (fun k => A k.succ) (fun k => B k.succ) (fun k => hA k.succ) (fun k => hB k.succ)
    have hBt : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) BT‖ ≤ (K + 1) ^ r := by
      exact orderedProduct_Euclidean_opNorm_le (K + 1) (by positivity) _
        (fun k => (hB k.succ).trans (le_add_of_nonneg_right (by positivity)))
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A 0 * AT - B 0 * BT)‖ ≤ _
    rw [he, map_add, map_mul, map_mul, Fin.sum_univ_succ]
    have ha := (norm_mul_le (Matrix.toEuclideanCLM (𝕜 := ℂ) (A 0))
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (AT - BT))).trans
      (mul_le_mul (hA 0) hAt (norm_nonneg _) hK)
    have hb := (norm_mul_le (Matrix.toEuclideanCLM (𝕜 := ℂ) (A 0 - B 0))
      (Matrix.toEuclideanCLM (𝕜 := ℂ) BT)).trans
      (mul_le_mul_of_nonneg_left hBt (norm_nonneg _))
    apply (norm_add_le _ _).trans ((add_le_add ha hb).trans ?_)
    rw [pow_succ]
    have hs : 0 ≤ ∑ k : Fin r, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k.succ - B k.succ)‖ :=
      Finset.sum_nonneg (fun k _ => norm_nonneg _)
    have hd : 0 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A 0 - B 0)‖ := norm_nonneg _
    have hp : 0 ≤ (K + 1) ^ r := by positivity
    nlinarith [mul_nonneg hp hs, mul_nonneg (mul_nonneg hK hp) hd]

/-- Actual normalized traces inherit the same finite perturbation bound. -/
theorem normalizedTrace_orderedProduct_sub_le {r : ℕ} (K : ℝ) (hK : 0 ≤ K)
    (A B : Fin r → Matrix n n ℂ)
    (hA : ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k)‖ ≤ K)
    (hB : ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖ ≤ K) :
    ‖normalizedTrace (List.ofFn A).prod - normalizedTrace (List.ofFn B).prod‖ ≤
      (K + 1) ^ r * ∑ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A k - B k)‖ := by
  have he : normalizedTrace (List.ofFn A).prod - normalizedTrace (List.ofFn B).prod =
      normalizedTrace ((List.ofFn A).prod - (List.ofFn B).prod) := by
    simp only [normalizedTrace, Matrix.trace_sub, mul_sub]
  rw [he]
  exact (normalizedTrace_norm_le_Euclidean_opNorm _).trans
    (orderedProduct_Euclidean_opNorm_sub_le K hK A B hA hB)

/-- Vanishing factorwise operator perturbations imply vanishing differences
of actual normalized ordered traces, even as the matrix dimension varies. -/
theorem tendsto_normalizedTrace_orderedProduct_sub {r : ℕ} (K : ℝ) (hK : 0 ≤ K)
    (A B : ∀ N : ℕ, Fin r → Matrix (Fin N) (Fin N) ℂ)
    (hA : ∀ N k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A N k)‖ ≤ K)
    (hB : ∀ N k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B N k)‖ ≤ K)
    (hd : ∀ k, Tendsto (fun N => ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A N k - B N k)‖) atTop (𝓝 0)) :
    Tendsto (fun N => normalizedTrace (List.ofFn (A N)).prod - normalizedTrace (List.ofFn (B N)).prod)
      atTop (𝓝 0) := by
  have hs : Tendsto (fun N => ∑ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A N k - B N k)‖)
      atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun k _ => hd k)
  apply squeeze_zero_norm' (Eventually.of_forall (fun N =>
    normalizedTrace_orderedProduct_sub_le K hK (A N) (B N) (hA N) (hB N)))
  simpa only [mul_zero] using tendsto_const_nhds.mul
    (f := fun _ : ℕ => (K + 1) ^ r) hs

/-- Centering finitely many uniformly bounded factors with vanishing actual
normalized traces changes the ordered normalized trace by a quantity tending to zero. -/
theorem tendsto_normalizedTrace_orderedProduct_center_sub {r : ℕ} (K : ℝ) (hK : 0 ≤ K)
    (A : ∀ N : ℕ, Fin r → Matrix (Fin N) (Fin N) ℂ)
    (hA : ∀ N k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A N k)‖ ≤ K)
    (ht : ∀ k, Tendsto (fun N => normalizedTrace (A N k)) atTop (𝓝 0)) :
    Tendsto (fun N => normalizedTrace (List.ofFn (A N)).prod -
      normalizedTrace (List.ofFn (fun k => matrixTraceCenter (A N k))).prod) atTop (𝓝 0) := by
  apply tendsto_normalizedTrace_orderedProduct_sub (2 * K) (by positivity) A
    (fun N k => matrixTraceCenter (A N k))
  · intro N k
    exact (hA N k).trans (by linarith)
  · intro N k
    exact (matrixTraceCenter_opNorm_le _).trans (mul_le_mul_of_nonneg_left (hA N k) (by positivity))
  · intro k
    apply squeeze_zero' (Eventually.of_forall (fun N => norm_nonneg _))
      (Eventually.of_forall (fun N => sub_matrixTraceCenter_opNorm_le _))
    exact tendsto_zero_iff_norm_tendsto_zero.mp (ht k)

end FreeProbability.Orthogonal
