import FreeProbability.Algebraic.Distribution
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Joint moment convergence

The source algebras may depend on the sequence index, as matrix dimension does.
Convergence is defined on all noncommuting polynomials and proved equivalent to
wordwise moment convergence. No uniform bounds or compact-support assumptions
are needed for this algebraic equivalence.
-/

namespace FreeProbability

open Filter Topology

variable {𝕜 A I N : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]
  [Ring A] [Algebra 𝕜 A] {D : N → Type*} [∀ n, Ring (D n)] [∀ n, Algebra 𝕜 (D n)]

/-- Joint convergence against all noncommuting polynomials along an arbitrary filter. -/
def ConvergesInDistribution (φn : ∀ n, ProbabilitySpace 𝕜 (D n))
    (an : ∀ n, I → D n) (φ : ProbabilitySpace 𝕜 A) (a : I → A) (l : Filter N) : Prop :=
  ∀ p : WordPolynomial 𝕜 I,
    Tendsto (fun n => jointDistribution (φn n) (an n) p) l (𝓝 (jointDistribution φ a p))

/-- Testing ordered words is equivalent to testing all noncommuting polynomials. -/
theorem convergesInDistribution_iff_moments (φn : ∀ n, ProbabilitySpace 𝕜 (D n))
    (an : ∀ n, I → D n) (φ : ProbabilitySpace 𝕜 A) (a : I → A) (l : Filter N) :
    ConvergesInDistribution φn an φ a l ↔
      ∀ w : List I, Tendsto (fun n => jointMoment (φn n) (an n) w) l (𝓝 (jointMoment φ a w)) := by
  constructor
  · intro h w
    simpa using h (MonoidAlgebra.single (FreeMonoid.ofList w) 1)
  · intro h p
    induction p using MonoidAlgebra.induction_linear with
    | zero => simpa using (tendsto_const_nhds : Tendsto (fun _ : N => (0 : 𝕜)) l (𝓝 0))
    | add p q hp hq => simpa only [map_add] using hp.add hq
    | single w c =>
      obtain ⟨w, rfl⟩ := FreeMonoid.ofList.surjective w
      simpa using (h w).const_mul c

/-- Star convergence is ordinary moment convergence of the doubled generator family. -/
def ConvergesInStarDistribution [Star A] [∀ n, Star (D n)]
    (φn : ∀ n, ProbabilitySpace 𝕜 (D n)) (an : ∀ n, I → D n)
    (φ : ProbabilitySpace 𝕜 A) (a : I → A) (l : Filter N) : Prop :=
  ConvergesInDistribution φn (fun n => starFamily (an n)) φ (starFamily a) l

/-- Changing the limiting realization to another with the same joint distribution
preserves convergence. -/
theorem ConvergesInDistribution.congr_limit {E : Type*} [Ring E] [Algebra 𝕜 E]
    {φn : ∀ n, ProbabilitySpace 𝕜 (D n)} {an : ∀ n, I → D n}
    {φ : ProbabilitySpace 𝕜 A} {a : I → A} {l : Filter N}
    (h : ConvergesInDistribution φn an φ a l) (ψ : ProbabilitySpace 𝕜 E) (b : I → E)
    (heq : SameDistribution φ ψ a b) : ConvergesInDistribution φn an ψ b l := by
  apply (convergesInDistribution_iff_moments _ _ _ _ _).mpr
  intro w
  rw [← heq w]
  exact (convergesInDistribution_iff_moments _ _ _ _ _).mp h w

end FreeProbability
