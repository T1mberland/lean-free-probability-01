import FreeProbability.Fock.OrnsteinUhlenbeckL2Cyclic
import Mathlib.Topology.EMetricSpace.Lipschitz

/-! # Uniform contraction and dense continuous orbits give genuine joint strong continuity -/
noncomputable section
open scoped Classical NNReal
namespace FreeProbability.Fock

section General
variable {Time E F : Type*} [TopologicalSpace Time]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The actual vectors whose orbit under a family of bounded linear maps is norm continuous. -/
def continuousOrbitSubmodule (A : Time → E →L[ℂ] F) : Submodule ℂ E where
  carrier := {x | Continuous (fun t => A t x)}
  zero_mem' := by
    change Continuous (fun t => A t 0)
    simpa only [map_zero] using (continuous_const : Continuous (fun _ : Time => (0 : F)))
  add_mem' {x y} hx hy := by
    change Continuous (fun t => A t (x + y))
    have heq : (fun t => A t (x + y)) = (fun t => A t x + A t y) :=
      funext (fun t => map_add (A t) x y)
    rw [heq]
    exact hx.add hy
  smul_mem' c x hx := by
    change Continuous (fun t => A t (c • x))
    have heq : (fun t => A t (c • x)) = (fun t => c • A t x) :=
      funext (fun t => map_smul (A t) c x)
    rw [heq]
    exact hx.const_smul c


/-- Genuine joint time/vector continuity from dense continuous orbits and a uniform contraction bound. -/
theorem continuous_contraction_family_of_dense (A : Time → E →L[ℂ] F)
    (hA : ∀ t x, ‖A t x‖ ≤ ‖x‖) {S : Set E} (hS : Dense S)
    (hC : ∀ x ∈ S, Continuous (fun t => A t x)) :
    Continuous (fun p : Time × E => A p.1 p.2) := by
  apply continuous_prod_of_dense_continuous_lipschitzWith' _ 1 hS
  · intro t
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    simpa only [NNReal.coe_one, one_mul] using hA t (x - y)
  · exact hC
omit [NormedSpace ℂ E] [NormedSpace ℂ F] in
/-- Restrict joint continuity to a fixed vector. -/
theorem continuous_orbit_of_joint (f : Time × E → F) (hf : Continuous f) (x : E) :
    Continuous (fun t => f (t, x)) := by
  exact hf.comp (continuous_id.prodMk continuous_const)
end General

variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual nonnegative-time native OU family of bounded linear maps. -/
def nativeOUOrbitFamily (e : I → H) (he : Orthonormal ℂ e) :
    ℝ≥0 → tensorFamilyAlgebra e →L[ℂ] tensorFamilyAlgebra e :=
  fun t => familyOUTimeContinuous e he t t.coe_nonneg

/-- Every actual closed Wick word has a norm-continuous time orbit. -/
theorem nativeOUOrbitFamily_continuous_Wick (e : I → H) (he : Orthonormal ℂ e) (w : List I) :
    Continuous (fun t : ℝ≥0 => nativeOUOrbitFamily e he t (familyClosedWick e w)) := by
  have hc : Continuous (fun t : ℝ≥0 => (Real.exp (-(t : ℝ)) : ℂ) ^ w.length • familyClosedWick e w) := by
    fun_prop
  have heq : (fun t : ℝ≥0 => nativeOUOrbitFamily e he t (familyClosedWick e w)) =
      (fun t : ℝ≥0 => (Real.exp (-(t : ℝ)) : ℂ) ^ w.length • familyClosedWick e w) := by
    funext t
    exact familyOUTime_Wick e he t t.coe_nonneg w
  rw [heq]
  exact hc

/-- The actual continuous native OU orbits form a dense subspace of the entire generated C-star closure. -/
theorem nativeOU_continuous_orbits_dense (e : I → H) (he : Orthonormal ℂ e) :
    Dense (continuousOrbitSubmodule (nativeOUOrbitFamily e he) : Set (tensorFamilyAlgebra e)) := by
  let C := continuousOrbitSubmodule (nativeOUOrbitFamily e he)
  let S := C.map (tensorFamilyAlgebra e).val.toLinearMap
  have hs : familyWickSpan e ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    exact Submodule.mem_map.mpr ⟨familyClosedWick e w, nativeOUOrbitFamily_continuous_Wick e he w, rfl⟩
  let P := StarAlgebra.adjoin ℂ (Set.range (tensorFamilyField e))
  let j : P → tensorFamilyAlgebra e := StarSubalgebra.inclusion P.le_topologicalClosure
  have hd : DenseRange j := by
    change DenseRange (Set.inclusion P.le_topologicalClosure)
    apply (denseRange_inclusion_iff P.le_topologicalClosure).mpr
    exact Set.Subset.rfl
  apply hd.mono
  rintro _ ⟨T, rfl⟩
  have hm : (T : TensorFullFock H →L[ℂ] TensorFullFock H) ∈ S :=
    hs (family_polynomial_mem_WickSpan e T.property)
  obtain ⟨U, hU, hval⟩ := Submodule.mem_map.mp hm
  have heq : U = j T := Subtype.ext hval
  rw [← heq]
  exact hU

/-- Genuine joint norm continuity in time and native C-star algebra element. -/
theorem familyOUTime_joint_continuous (e : I → H) (he : Orthonormal ℂ e) :
    Continuous (fun p : ℝ≥0 × tensorFamilyAlgebra e => familyOUTime e he p.1 p.1.coe_nonneg p.2) := by
  apply continuous_contraction_family_of_dense (nativeOUOrbitFamily e he)
    (fun t T => norm_familyOUTime_le e he t t.coe_nonneg T) (nativeOU_continuous_orbits_dense e he)
  intro T hT
  exact hT

/-- Actual strong time continuity on the whole native C-star closure, including at time zero. -/
theorem familyOUTime_strong_continuous (e : I → H) (he : Orthonormal ℂ e) (T : tensorFamilyAlgebra e) :
    Continuous (fun t : ℝ≥0 => familyOUTime e he t t.coe_nonneg T) := by
  exact continuous_orbit_of_joint _ (familyOUTime_joint_continuous e he) T

end FreeProbability.Fock
