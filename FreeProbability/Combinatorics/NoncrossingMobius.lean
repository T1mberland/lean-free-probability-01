import FreeProbability.Combinatorics.RefinementMomentCumulant
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra

/-!
# Möbius inversion of free cumulants on the noncrossing lattice

The actual finite refinement lattice carries mathlib's incidence-algebra Möbius
function. Applying its inversion theorem to the proved full lower-interval
moment–cumulant convolution gives all partition cumulants, and the scalar top
cumulant, as Möbius-weighted multiplicative moments.
-/

namespace FreeProbability

variable {n : ℕ}

noncomputable instance : LocallyFiniteOrder (NoncrossingPartition n) := by
  classical
  exact Fintype.toLocallyFiniteOrder

/-- The incidence-algebra Möbius function of the noncrossing refinement lattice. -/
noncomputable def noncrossingMobius (𝕜 : Type*) [Ring 𝕜]
    (p q : NoncrossingPartition n) : 𝕜 := by
  classical
  exact IncidenceAlgebra.mu 𝕜 p q

variable {X 𝕜 : Type*} [Field 𝕜]

/-- The multiplicative cumulant contribution is the actual lattice Möbius inversion
of multiplicative moments, at every partition. -/
theorem partitionCumulant_eq_mobius_sum (M : List X → 𝕜) (h0 : M [] = 1)
    (w : List X) (p : NoncrossingPartition w.length) :
    partitionContribution (freeCumulant M) w p =
      ∑ q ∈ Finset.Iic p, noncrossingMobius 𝕜 q p * partitionContribution M w q := by
  classical
  unfold noncrossingMobius
  refine IncidenceAlgebra.moebius_inversion_bot
    (fun q => partitionContribution (freeCumulant M) w q)
    (fun q => partitionContribution M w q) ?_ p
  intro q
  rw [Finset.sum_subtype (Finset.Iic q) (fun r => Finset.mem_Iic)
    (fun r => partitionContribution (freeCumulant M) w r)]
  exact partitionMoment_eq_sum_refinementCumulants M h0 w q

/-- Every nonempty free cumulant is its Möbius-weighted noncrossing moment sum. -/
theorem freeCumulant_eq_mobius_sum (M : List X → 𝕜) (h0 : M [] = 1)
    (w : List X) (hw : w ≠ []) :
    freeCumulant M w = ∑ p : NoncrossingPartition w.length,
      noncrossingMobius 𝕜 p ⊤ * partitionContribution M w p := by
  classical
  have h := partitionCumulant_eq_mobius_sum M h0 w (⊤ : NoncrossingPartition w.length)
  have ht : partitionContribution (freeCumulant M) w (⊤ : NoncrossingPartition w.length) =
      freeCumulant M w := by
    rw [NoncrossingPartition.top_eq_indiscrete]
    exact partitionContribution_indiscrete _ w hw
  rw [ht, Finset.Iic_top] at h
  exact h

/-- The corresponding Möbius formula for cumulants of actual algebraic expectations. -/
theorem cumulant_eq_mobius_sum {A : Type*} [Ring A] [Algebra 𝕜 A]
    (φ : ProbabilitySpace 𝕜 A) (w : List A) (hw : w ≠ []) :
    cumulant φ w = ∑ p : NoncrossingPartition w.length,
      noncrossingMobius 𝕜 p ⊤ * partitionContribution (fun v => φ.expectation v.prod) w p :=
  freeCumulant_eq_mobius_sum _ φ.map_one w hw

end FreeProbability
