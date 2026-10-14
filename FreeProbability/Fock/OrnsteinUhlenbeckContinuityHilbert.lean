import FreeProbability.Fock.OrnsteinUhlenbeckContinuityDense

/-! # Actual strong continuity on the complete tensor Hilbert sum and cyclic L² closure -/
noncomputable section
open scoped Classical NNReal ENNReal
namespace FreeProbability.Fock
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual nonnegative-time damping family on the full complete tensor Hilbert sum. -/
def tensorDampingOrbitFamily : ℝ≥0 → TensorFullFock H →L[ℂ] TensorFullFock H :=
  fun t => degreeDamping H t t.coe_nonneg

/-- Every complete homogeneous sector vector has a norm-continuous degree-damping orbit. -/
theorem tensorDampingOrbitFamily_continuous_single (n : ℕ) (f : TensorPower H n) :
    Continuous (fun t : ℝ≥0 => tensorDampingOrbitFamily H t (lp.single 2 n f)) := by
  have hc : Continuous (fun t : ℝ≥0 => (Real.exp (-(t : ℝ)) : ℂ) ^ n • lp.single (E := fun n => TensorPower H n) 2 n f) := by
    fun_prop
  have heq : (fun t : ℝ≥0 => tensorDampingOrbitFamily H t (lp.single 2 n f)) =
      (fun t : ℝ≥0 => (Real.exp (-(t : ℝ)) : ℂ) ^ n • lp.single 2 n f) := by
    funext t
    exact degreeDamping_single H t t.coe_nonneg n f
  rw [heq]
  exact hc

/-- Continuous damping orbits are dense by actual convergence of infinite Hilbert-sector sums. -/
theorem tensorDamping_continuous_orbits_dense :
    Dense (continuousOrbitSubmodule (tensorDampingOrbitFamily H) : Set (TensorFullFock H)) := by
  let C := continuousOrbitSubmodule (tensorDampingOrbitFamily H)
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro f
  have hc := C.isClosed_topologicalClosure
  have hs : ∀ s : Finset ℕ, (∑ n ∈ s, lp.single 2 n (f n)) ∈ C.topologicalClosure := by
    intro s
    apply C.topologicalClosure.sum_mem
    intro n _
    exact C.le_topologicalClosure (tensorDampingOrbitFamily_continuous_single H n (f n))
  have hm := hc.mem_of_tendsto (lp.hasSum_single (ENNReal.ofNat_ne_top (n := 2)) f)
    (Filter.Eventually.of_forall hs)
  exact hm

/-- Genuine joint time/vector norm continuity for arbitrary infinite completed tensor sums. -/
theorem degreeDamping_joint_continuous :
    Continuous (fun p : ℝ≥0 × TensorFullFock H => degreeDamping H p.1 p.1.coe_nonneg p.2) := by
  apply continuous_contraction_family_of_dense (tensorDampingOrbitFamily H)
    (fun t f => norm_degreeDamping_le H t t.coe_nonneg f) (tensorDamping_continuous_orbits_dense H)
  intro f hf
  exact hf

/-- Actual strong time continuity of complete Hilbert degree damping, including time zero. -/
theorem degreeDamping_strong_continuous (f : TensorFullFock H) :
    Continuous (fun t : ℝ≥0 => degreeDamping H t t.coe_nonneg f) :=
  continuous_orbit_of_joint _ (degreeDamping_joint_continuous H) f

variable {H} {I : Type*}

/-- The genuine cyclic Hilbert OU extension has joint norm continuity in time and vector. -/
theorem familyOUL2_joint_continuous (e : I → H) (he : Orthonormal ℂ e) :
    Continuous (fun p : ℝ≥0 × familyCyclicSpace e => familyOUL2 e he p.1 p.1.coe_nonneg p.2) := by
  apply continuous_induced_rng.mpr
  have hc : Continuous (fun p : ℝ≥0 × familyCyclicSpace e =>
      (p.1, (p.2 : TensorFullFock H))) := continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  exact (degreeDamping_joint_continuous H).comp hc

/-- Actual strong time continuity of the L² extension on the whole complete cyclic Hilbert space. -/
theorem familyOUL2_strong_continuous (e : I → H) (he : Orthonormal ℂ e) (f : familyCyclicSpace e) :
    Continuous (fun t : ℝ≥0 => familyOUL2 e he t t.coe_nonneg f) :=
  continuous_orbit_of_joint _ (familyOUL2_joint_continuous e he) f

end FreeProbability.Fock
