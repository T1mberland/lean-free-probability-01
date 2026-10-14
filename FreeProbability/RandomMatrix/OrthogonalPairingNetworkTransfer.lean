import FreeProbability.RandomMatrix.OrthogonalPairingNetworkTransferColorings
import FreeProbability.RandomMatrix.OrthogonalTraceContractions
import FreeProbability.RandomMatrix.OrthogonalPermutationNetworkTrace

/-! # Exact actual pairing networks as oriented permutation networks -/

noncomputable section
open scoped Classical
namespace FreeProbability.Orthogonal
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The literal ordinary pairing delta tests actual compatible colorings. -/
theorem ordinaryPairingDelta_eq_indicator {r : ℕ} (p : OrdinaryPairing r)
    (i : Fin (2 * r) → n) :
    ordinaryPairingDelta p i = if pairingSetoid p.out ≤ Setoid.ker i then 1 else 0 := by
  simpa only [pairingTensor_coefficient, ordinaryPairingDelta] using
    pairingTensor_coefficient_indicator (n := n) p.out i

/-- A genuine paired deterministic network with arbitrary complex matrices. -/
def pairingNetwork {r : ℕ} (p : OrdinaryPairing r) (e : PairingSites r)
    (M : Fin r → Matrix n n ℂ) : ℂ :=
  ∑ i : Fin (2 * r) → n, (∏ k, M k (i (e.symm (k, 0))) (i (e.symm (k, 1)))) *
    (ordinaryPairingDelta p i : ℂ)

/-- Removing the genuine paired delta gives exactly the actual compatible
colorings, rather than a supplied coloring constraint. -/
theorem pairingNetwork_eq_sum_compatible {r : ℕ} (p : OrdinaryPairing r) (e : PairingSites r)
    (M : Fin r → Matrix n n ℂ) :
    pairingNetwork p e M = ∑ i : PairingCompatibleColorings p n,
      ∏ k, M k (i.val (e.symm (k, 0))) (i.val (e.symm (k, 1))) := by
  let f : (Fin (2 * r) → n) → ℂ := fun i => ∏ k, M k (i (e.symm (k, 0))) (i (e.symm (k, 1)))
  change (∑ i, f i * (ordinaryPairingDelta p i : ℂ)) = ∑ i : PairingCompatibleColorings p n, f i.val
  simp_rw [ordinaryPairingDelta_eq_indicator]
  simp only [apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_zero, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun i => by simp) f

/-- Every selected edge carries its actual matrix or transpose, according
to its genuine chosen endpoint orientation. -/
def pairingOrientedMatrix {r : ℕ} (p : OrdinaryPairing r) (e : PairingSites r)
    (M : Fin r → Matrix n n ℂ) (a : PairingHalfSites p (Quotient.mk _ e)) : Matrix n n ℂ :=
  if (e a.val).2 = 0 then M (e a.val).1 else (M (e a.val).1).transpose

omit [Fintype n] [DecidableEq n] in
/-- The coordinate rule is exactly the earlier proved orientation bit. -/
theorem pairingOrientedMatrix_selected {r : ℕ} (p : OrdinaryPairing r) (e : PairingSites r)
    (M : Fin r → Matrix n n ℂ) (k : Fin r) :
    pairingOrientedMatrix p e M (pairingSelectedEndpoint p e k) =
      if pairingEdgeOrientation p e k then (M k).transpose else M k := by
  unfold pairingOrientedMatrix
  rw [pairingSelectedEndpoint_coordinate]
  cases h : pairingEdgeOrientation p e k <;> simp

private theorem edge_partner {r : ℕ} (e : PairingSites r) (k : Fin r) (b : Fin 2) :
    pairingPartner (Quotient.mk _ e) (e.symm (k, b)) = e.symm (k, Equiv.swap 0 1 b) := by
  rw [pairingPartner_mk]
  simp [codePairingPartner]

omit [Fintype n] [DecidableEq n] in
private theorem compatible_next {r : ℕ} (p q : OrdinaryPairing r)
    (i : PairingCompatibleColorings p n) (a : PairingHalfSites p q) :
    i.val (pairingHalfPermutation p q a).val = i.val (pairingPartner q a.val) :=
  (i.property (pairingPartner_related p (pairingPartner q a.val))).symm

omit [Fintype n] [DecidableEq n] in
/-- The ACTUAL oriented entry preserves the original complex scalar,
including transpose orientation and the genuine next selected site. -/
theorem pairingOrientedMatrix_entry {r : ℕ} (p : OrdinaryPairing r) (e : PairingSites r)
    (M : Fin r → Matrix n n ℂ) (i : PairingCompatibleColorings p n)
    (a : PairingHalfSites p (Quotient.mk _ e)) :
    pairingOrientedMatrix p e M a (i.val a.val)
      (i.val (pairingHalfPermutation p (Quotient.mk _ e) a).val) =
      M (e a.val).1 (i.val (e.symm ((e a.val).1, 0))) (i.val (e.symm ((e a.val).1, 1))) := by
  rw [compatible_next]
  let k := (e a.val).1
  have ha : a.val = e.symm (k, (e a.val).2) := by simp only [k, Prod.mk.eta, Equiv.symm_apply_apply]
  change (if (e a.val).2 = 0 then M k else (M k).transpose) (i.val a.val)
    (i.val (pairingPartner (Quotient.mk _ e) a.val)) =
    M k (i.val (e.symm (k, 0))) (i.val (e.symm (k, 1)))
  have hb : (e a.val).2 = 0 ∨ (e a.val).2 = 1 := by omega
  rcases hb with hb | hb
  · have h0 : a.val = e.symm (k, 0) := ha.trans (congrArg (fun b => e.symm (k, b)) hb)
    have h1 : pairingPartner (Quotient.mk _ e) a.val = e.symm (k, 1) := by
      rw [h0, edge_partner, Equiv.swap_apply_left]
    rw [hb]
    simp only [ite_true]
    rw [h1, h0]
  · have h1 : a.val = e.symm (k, 1) := ha.trans (congrArg (fun b => e.symm (k, b)) hb)
    have h0 : pairingPartner (Quotient.mk _ e) a.val = e.symm (k, 0) := by
      rw [h1, edge_partner, Equiv.swap_apply_right]
    rw [hb]
    simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false, Matrix.transpose_apply]
    rw [h0, h1]

/-- Genuine edge exhaustion transfers the paired network to the actual
selected-half permutation network, preserving complex phases. -/
theorem pairingNetwork_eq_oriented_permutationNetwork {r : ℕ} (p : OrdinaryPairing r)
    (e : PairingSites r) (M : Fin r → Matrix n n ℂ) :
    pairingNetwork p e M = permutationNetwork (pairingHalfPermutation p (Quotient.mk _ e))
      (pairingOrientedMatrix p e M) := by
  let : DecidableEq (PairingHalfSites p (Quotient.mk _ e)) := Classical.decEq _
  rw [pairingNetwork_eq_sum_compatible]
  let F : PairingCompatibleColorings p n → ℂ := fun i =>
    ∏ k, M k (i.val (e.symm (k, 0))) (i.val (e.symm (k, 1)))
  let G : (PairingHalfSites p (Quotient.mk _ e) → n) → ℂ := fun u =>
    ∏ a, pairingOrientedMatrix p e M a (u a) (u (pairingHalfPermutation p (Quotient.mk _ e) a))
  unfold permutationNetwork
  change (∑ i : PairingCompatibleColorings p n, F i) = ∑ u : PairingHalfSites p (Quotient.mk _ e) → n, G u
  rw [← Equiv.sum_comp (pairingCompatibleColoringsEquiv p (Quotient.mk _ e) n)]
  apply Finset.sum_congr rfl
  intro i _
  change (∏ k, M k (i.val (e.symm (k, 0))) (i.val (e.symm (k, 1)))) =
    ∏ a : PairingHalfSites p (Quotient.mk _ e), pairingOrientedMatrix p e M a
      (i.val a.val) (i.val (pairingHalfPermutation p (Quotient.mk _ e) a).val)
  simp_rw [pairingOrientedMatrix_entry]
  rw [← Equiv.prod_comp (pairingEdgeHalfEquiv p e)]
  apply Finset.prod_congr rfl
  intro k _
  rw [pairingEdgeHalfEquiv_apply, pairingSelectedEndpoint_coordinate]

/-- Genuine paired networks therefore have their actual ordered cycle-trace
formula, with ALL selected singleton cycles retained. -/
theorem pairingNetwork_eq_prod_cycle_traces {r : ℕ} (p : OrdinaryPairing r) (e : PairingSites r)
    (M : Fin r → Matrix n n ℂ) :
    pairingNetwork p e M =
      ∏ c : PermutationOrbitIndex (pairingHalfPermutation p (Quotient.mk _ e)), Matrix.trace
        (List.ofFn (fun k => pairingOrientedMatrix p e M
          (permutationOrbitEnumeration (pairingHalfPermutation p (Quotient.mk _ e)) c k).val)).prod := by
  rw [pairingNetwork_eq_oriented_permutationNetwork, permutationNetwork_eq_prod_cycle_traces]

/-- The actual trace-word column network is a genuine paired network for the
literal deterministic-edge site code. -/
def traceColumnEdgeCode (r : ℕ) : PairingSites r where
  toFun a := (traceSites r a).elim (fun k => (k, 0)) (fun k => (k, 1))
  invFun z := if z.2 = 0 then (traceSites r).symm (.inl z.1) else (traceSites r).symm (.inr z.1)
  left_inv a := by
    obtain ⟨a, rfl⟩ := (traceSites r).symm.surjective a
    cases a <;> simp
  right_inv z := by
    rcases z with ⟨k, b⟩
    fin_cases b <;> simp


theorem traceColumnEdgeCode_symm_zero (r : ℕ) (k : Fin r) :
    (traceColumnEdgeCode r).symm (k, 0) = (traceSites r).symm (.inl k) := by
  simp [traceColumnEdgeCode]

theorem traceColumnEdgeCode_symm_one (r : ℕ) (k : Fin r) :
    (traceColumnEdgeCode r).symm (k, 1) = (traceSites r).symm (.inr k) := by
  simp [traceColumnEdgeCode]

/-- The existing actual trace-word column network is the transferred genuine
paired network for its literal deterministic edge code. -/
theorem traceColumnNetwork_eq_pairingNetwork {r : ℕ} (A : Fin r → Matrix n n ℂ)
    (q : OrdinaryPairing r) :
    traceColumnNetwork A q = pairingNetwork q (traceColumnEdgeCode r) A := by
  unfold traceColumnNetwork pairingNetwork
  simp only [traceColumnEdgeCode_symm_zero, traceColumnEdgeCode_symm_one]

/-- Actual column networks inherit the proved phase-preserving permutation
network transfer, without assuming a cycle identity. -/
theorem traceColumnNetwork_eq_oriented_permutationNetwork {r : ℕ}
    (A : Fin r → Matrix n n ℂ) (q : OrdinaryPairing r) :
    traceColumnNetwork A q =
      permutationNetwork (pairingHalfPermutation q (Quotient.mk _ (traceColumnEdgeCode r)))
        (pairingOrientedMatrix q (traceColumnEdgeCode r) A) := by
  rw [traceColumnNetwork_eq_pairingNetwork, pairingNetwork_eq_oriented_permutationNetwork]

end FreeProbability.Orthogonal
