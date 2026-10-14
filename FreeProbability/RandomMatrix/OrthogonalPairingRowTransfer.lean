import FreeProbability.RandomMatrix.OrthogonalPairingNetworkTransferNorm

/-! # Genuine cyclic deterministic-edge code for the actual row network -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal
open Matrix

/-- The actual row edges go from right k to left(next k). -/
def traceRowEdgeCode (r : ℕ) : PairingSites r where
  toFun a := (traceSites r a).elim (fun k => ((finRotate r).symm k, 1)) (fun k => (k, 0))
  invFun z := if z.2 = 0 then (traceSites r).symm (.inr z.1)
    else (traceSites r).symm (.inl (finRotate r z.1))
  left_inv a := by
    obtain ⟨a, rfl⟩ := (traceSites r).symm.surjective a
    cases a <;> simp [-finRotate_apply, -finRotate_symm_apply]
  right_inv z := by
    rcases z with ⟨k, b⟩
    fin_cases b <;> simp [-finRotate_apply, -finRotate_symm_apply]

theorem traceRowEdgeCode_symm_zero (r : ℕ) (k : Fin r) :
    (traceRowEdgeCode r).symm (k, 0) = (traceSites r).symm (.inr k) := by
  simp [traceRowEdgeCode]

theorem traceRowEdgeCode_symm_one (r : ℕ) (k : Fin r) :
    (traceRowEdgeCode r).symm (k, 1) = (traceSites r).symm (.inl (finRotate r k)) := by
  simp [traceRowEdgeCode]

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The existing row network is EXACTLY the genuine paired network of its
cyclic edge code. Complex scalar phases are preserved. -/
theorem traceRowNetwork_eq_pairingNetwork {r : ℕ} (B : Fin r → Matrix n n ℂ)
    (p : OrdinaryPairing r) :
    traceRowNetwork B p = pairingNetwork p (traceRowEdgeCode r) B := by
  unfold traceRowNetwork pairingNetwork
  simp only [traceRowEdgeCode_symm_zero, traceRowEdgeCode_symm_one]

/-- The genuine row network has one dimension factor per actual raw loop. -/
theorem traceRowNetwork_norm_le {r : ℕ} (B : Fin r → Matrix n n ℂ) (p : OrdinaryPairing r) :
    ‖traceRowNetwork B p‖ ≤
      (Fintype.card n : ℝ) ^ pairingLoopCount p (Quotient.mk _ (traceRowEdgeCode r)) *
        ∏ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (B k)‖ := by
  rw [traceRowNetwork_eq_pairingNetwork]
  exact pairingNetwork_norm_le _ _ _

end FreeProbability.Orthogonal
