import FreeProbability.Combinatorics.CumulantNaturality
import FreeProbability.Combinatorics.CumulantConvergence

/-!
# Univariate cumulants from power moments

Equal power moments determine equal univariate cumulants across different ambient
algebras. Along arbitrary filters and varying source algebras, power-moment
convergence is equivalent to convergence of all univariate cumulants.
-/

namespace FreeProbability

open Filter Topology

variable {𝕜 A E : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A] [Ring E] [Algebra 𝕜 E]

/-- Inverting the power-moment function on one-letter words gives the univariate cumulants. -/
theorem freeCumulant_powerMoments (φ : ProbabilitySpace 𝕜 A) (a : A) (w : List Unit) :
    freeCumulant (fun v : List Unit => φ.expectation (a ^ v.length)) w =
      cumulant φ (List.replicate w.length a) := by
  have hm : (fun v : List A => φ.expectation v.prod) ∘ List.map (fun _ : Unit => a) =
      (fun v : List Unit => φ.expectation (a ^ v.length)) := by
    funext v
    simp [Function.comp_apply, List.map_const', List.prod_replicate]
  rw [← hm, freeCumulant_map]
  simp only [List.map_const', cumulant]

/-- Equality of all power moments implies equality of all univariate cumulants. -/
theorem cumulant_replicate_eq_of_powerMoments (φ : ProbabilitySpace 𝕜 A)
    (ψ : ProbabilitySpace 𝕜 E) (a : A) (b : E)
    (h : ∀ n, φ.expectation (a ^ n) = ψ.expectation (b ^ n)) (n : ℕ) :
    cumulant φ (List.replicate n a) = cumulant ψ (List.replicate n b) := by
  have hm : (fun v : List Unit => φ.expectation (a ^ v.length)) =
      (fun v : List Unit => ψ.expectation (b ^ v.length)) := funext (fun v => h v.length)
  have hk := congrArg (fun M => freeCumulant M (List.replicate n ())) hm
  simpa only [freeCumulant_powerMoments, List.length_replicate] using hk

/-- Power moments converge exactly when all univariate cumulants converge,
with no boundedness assumptions and allowing different source algebras. -/
theorem powerMoments_tendsto_iff_cumulants {T : Type*} {D : T → Type*}
    [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] [∀ t, Ring (D t)] [∀ t, Algebra 𝕜 (D t)]
    (φt : ∀ t, ProbabilitySpace 𝕜 (D t)) (aSource : ∀ t, D t)
    (φ : ProbabilitySpace 𝕜 A) (a : A) (l : Filter T) :
    (∀ n, Tendsto (fun t => (φt t).expectation (aSource t ^ n)) l (𝓝 (φ.expectation (a ^ n)))) ↔
      ∀ n, Tendsto (fun t => cumulant (φt t) (List.replicate n (aSource t))) l
        (𝓝 (cumulant φ (List.replicate n a))) := by
  let M (t : T) (w : List Unit) := (φt t).expectation (aSource t ^ w.length)
  let L (w : List Unit) := φ.expectation (a ^ w.length)
  have hnorm : ∀ t, M t [] = 1 := fun t => by simp [M]
  have hLnorm : L [] = 1 := by simp [L]
  constructor
  · intro h n
    have hm : ∀ w, Tendsto (fun t => M t w) l (𝓝 (L w)) := fun w => h w.length
    have hk := tendsto_freeCumulant_of_moments M L l hm (List.replicate n ())
    simpa only [M, L, freeCumulant_powerMoments, List.length_replicate] using hk
  · intro h n
    have hk : ∀ w, Tendsto (fun t => freeCumulant (M t) w) l (𝓝 (freeCumulant L w)) := by
      intro w
      simpa only [M, L, freeCumulant_powerMoments] using h w.length
    have hm := tendsto_moments_of_freeCumulants M L l hnorm hLnorm hk (List.replicate n ())
    simpa only [M, L, List.length_replicate] using hm

end FreeProbability
