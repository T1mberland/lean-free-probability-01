import FreeProbability.Combinatorics.NoncrossingPairingDecomposition
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Weighted noncrossing pairing sums

Each actual two-point block contributes its weight once, at its lower endpoint.
First-partner splitting factors these products and gives the joint Wick recursion.
No probabilistic law is assumed by this combinatorial module.
-/

noncomputable section
open scoped Classical BigOperators

namespace FreeProbability.NoncrossingPairing

variable {m n : ℕ} {M : Type*}

/-- Product of one covariance weight per actual pair, selected at its smaller endpoint. -/
def pairingWeight [CommMonoid M] (p : NoncrossingPairing n) (C : Fin n → Fin n → M) : M :=
  ∏ a, if a < p.partner a then C a (p.partner a) else 1

/-- Smaller endpoints select exactly one representative of every actual pair. -/
def lowerEndpoints (p : NoncrossingPairing n) : Finset (Fin n) :=
  Finset.univ.filter (fun a => a < p.partner a)

/-- Actual pairs, represented with their endpoints in increasing order. -/
def pairingPairs (p : NoncrossingPairing n) : Finset (Fin n × Fin n) :=
  (lowerEndpoints p).image (fun a => (a, p.partner a))

/-- These pairs are exactly the distinct related endpoint pairs in increasing order. -/
theorem mem_pairingPairs (p : NoncrossingPairing n) (a b : Fin n) :
    (a, b) ∈ pairingPairs p ↔ a < b ∧ p.val.val.r a b := by
  constructor
  · intro h
    obtain ⟨c, hc, he⟩ := Finset.mem_image.mp h
    have he₁ := congrArg Prod.fst he
    have he₂ := congrArg Prod.snd he
    simp only at he₁ he₂
    subst c b
    exact ⟨(Finset.mem_filter.mp hc).2, p.rel_partner a⟩
  · rintro ⟨hab, hr⟩
    have he : b = p.partner a := ((p.rel_iff a b).mp hr).resolve_left (ne_of_gt hab)
    subst b
    exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, hab⟩, rfl⟩

/-- The endpoint-selected product is literally the product over all actual pairs. -/
theorem pairingWeight_eq_prod_pairs [CommMonoid M] (p : NoncrossingPairing n)
    (C : Fin n → Fin n → M) :
    pairingWeight p C = ∏ e ∈ pairingPairs p, C e.1 e.2 := by
  unfold pairingPairs
  rw [Finset.prod_image]
  · exact (Finset.prod_filter (fun a => a < p.partner a) (fun a => C a (p.partner a))).symm
  · intro a ha b hb he
    exact congrArg Prod.fst he

/-- Gluing contributes the outer pair and the two local pairing products. -/
theorem pairingWeight_glue [CommMonoid M] (k : Fin (n + 1))
    (L : NoncrossingPairing k.val) (R : NoncrossingPairing (n - k.val))
    (C : Fin (n + 2) → Fin (n + 2) → M) :
    pairingWeight (glue k L R) C = C 0 (splitPartner k) *
      pairingWeight L (fun a b => C (insideEmbedding k a) (insideEmbedding k b)) *
      pairingWeight R (fun a b => C (outsideEmbedding k a) (outsideEmbedding k b)) := by
  unfold pairingWeight
  rw [prod_splitPositions k]
  have h0 : (0 : Fin (n + 2)) < splitPartner k := by change 0 < k.val + 1; omega
  have hq : ¬splitPartner k < (0 : Fin (n + 2)) := not_lt_of_ge (Fin.zero_le _)
  simp only [partner_glue, gluedPartner_zero, gluedPartner_splitPartner,
    gluedPartner_inside, gluedPartner_outside, h0, hq, ite_true, ite_false, mul_one,
    (insideEmbedding k).lt_iff_lt, (outsideEmbedding k).lt_iff_lt]

/-- The weighted sum over actual noncrossing pairings. -/
def pairingSum [CommSemiring M] (C : Fin n → Fin n → M) : M :=
  ∑ p : NoncrossingPairing n, pairingWeight p C

/-- Full first-partner Wick recursion for arbitrary covariance weights. -/
theorem pairingSum_succ_succ [CommSemiring M] (C : Fin (n + 2) → Fin (n + 2) → M) :
    pairingSum C = ∑ k : Fin (n + 1), C 0 (splitPartner k) *
      pairingSum (fun a b => C (insideEmbedding k a) (insideEmbedding k b)) *
      pairingSum (fun a b => C (outsideEmbedding k a) (outsideEmbedding k b)) := by
  unfold pairingSum
  have h := Fintype.sum_equiv (firstPartnerEquiv n).symm
    (fun x => pairingWeight (glue x.1 x.2.1 x.2.2) C)
    (fun p => pairingWeight p C) (fun _ => rfl)
  rw [← h, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Fintype.sum_prod_type]
  simp_rw [pairingWeight_glue, ← Finset.mul_sum]
  rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- The unique empty pairing, with no blocks. -/
def emptyPairing : NoncrossingPairing 0 :=
  ⟨NoncrossingPartition.discrete 0, by
    intro s hs
    rw [NoncrossingPartition.blocks_zero] at hs
    simp at hs⟩

@[simp] theorem pairingSum_zero [CommSemiring M] (C : Fin 0 → Fin 0 → M) : pairingSum C = 1 := by
  let : Unique (NoncrossingPairing 0) := ⟨⟨emptyPairing⟩, fun p => Subsingleton.elim p _⟩
  simp [pairingSum, pairingWeight]

@[simp] theorem pairingSum_one [CommSemiring M] (C : Fin 1 → Fin 1 → M) : pairingSum C = 0 := by
  let : IsEmpty (NoncrossingPairing 1) := ⟨fun p =>
    not_nonempty_of_odd (by decide : Odd 1) ⟨p⟩⟩
  simp [pairingSum]

end FreeProbability.NoncrossingPairing

