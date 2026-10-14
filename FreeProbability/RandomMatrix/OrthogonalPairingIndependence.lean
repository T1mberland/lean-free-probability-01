import FreeProbability.RandomMatrix.OrthogonalPairingGram
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-! # Intrinsic ordinary pairing tensors are independent in stable dimension -/

noncomputable section
open scoped Classical RealInnerProductSpace
namespace FreeProbability.Orthogonal
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Intrinsic pairings identify codes with the SAME ordinary pairing relation,
removing the redundant pair numbering and orientations before independence. -/
abbrev OrdinaryPairing (r : ℕ) :=
  Quotient (Setoid.ker (pairingSetoid : PairingSites r → Setoid (Fin (2 * r))))

/-- The genuine tensor of an intrinsic ordinary pairing. -/
def ordinaryPairingTensor {r : ℕ} (p : OrdinaryPairing r) : EuclideanSpace ℝ (Fin (2 * r) → n) :=
  pairingTensor p.out

private theorem pairingSetoid_le_iff_eq {r : ℕ} (e f : PairingSites r) :
    pairingSetoid e ≤ pairingSetoid f ↔ pairingSetoid e = pairingSetoid f := by
  constructor
  · intro h
    let q : Quotient (pairingSetoid e) → Quotient (pairingSetoid f) := Quotient.map id (fun _ _ hrel => h hrel)
    have hs : Function.Surjective q := by
      intro x
      induction x using Quotient.inductionOn with
      | h a => exact ⟨Quotient.mk _ a, rfl⟩
    have hi : Function.Injective q := by
      by_contra hn
      have hc := Fintype.card_lt_of_surjective_not_injective q hs hn
      rw [card_pairingSetoid_quotient, card_pairingSetoid_quotient] at hc
      exact (lt_irrefl r) hc
    apply le_antisymm h
    intro a b hab
    exact Quotient.exact (hi (show q (Quotient.mk _ a) = q (Quotient.mk _ b) from Quotient.sound hab))
  · intro h
    exact h.le

private theorem ordinaryPairing_eq_of_setoid_eq {r : ℕ} {p q : OrdinaryPairing r}
    (h : pairingSetoid p.out = pairingSetoid q.out) : p = q := by
  have he : (Quotient.mk _ p.out : OrdinaryPairing r) = Quotient.mk _ q.out := Quotient.sound h
  simpa only [Quotient.out_eq] using he

/-- Actual coordinate evaluation isolates a single intrinsic pairing if pair
labels are distinct; this is the mathematical source of stable independence. -/
theorem ordinaryPairingTensor_isolating_coefficient {r : ℕ} (b : Fin r ↪ n)
    (p q : OrdinaryPairing r) :
    (ordinaryPairingTensor (n := n) q) (pairingTuple p.out b) = if q = p then (1 : ℝ) else 0 := by
  have hk : Setoid.ker (pairingTuple p.out b) = pairingSetoid p.out := by
    ext a c
    change b (p.out a).1 = b (p.out c).1 ↔ (p.out a).1 = (p.out c).1
    exact b.injective.eq_iff
  rw [ordinaryPairingTensor, pairingTensor_coefficient_indicator, hk, pairingSetoid_le_iff_eq]
  have he : pairingSetoid q.out = pairingSetoid p.out ↔ q = p :=
    ⟨ordinaryPairing_eq_of_setoid_eq, fun h => by subst q; rfl⟩
  simp only [he]

/-- Genuine independence of ALL intrinsic ordinary pairing vectors in
stable dimension N >= r, without assuming invariant-tensor spanning. -/
theorem ordinaryPairingTensor_linearIndependent (r : ℕ) (hr : r ≤ Fintype.card n) :
    LinearIndependent ℝ (ordinaryPairingTensor (n := n) (r := r)) := by
  obtain ⟨b : Fin r ↪ n⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin r) ≤ Fintype.card n by simpa using hr)
  rw [Fintype.linearIndependent_iff]
  intro c hc p
  have he := congrArg (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (2 * r) → n => ℝ) (pairingTuple p.out b)) hc
  simp only [map_sum, map_smul, map_zero] at he
  change (∑ q : OrdinaryPairing r, c q * (ordinaryPairingTensor q) (pairingTuple p.out b)) = 0 at he
  simp only [ordinaryPairingTensor_isolating_coefficient] at he
  simpa using he
end FreeProbability.Orthogonal
