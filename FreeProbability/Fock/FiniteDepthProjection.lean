import FreeProbability.Fock.OrnsteinUhlenbeckVonNeumannFiniteRankApproximation

/-! # Actual finite-length Fock projections and complete-space convergence -/
noncomputable section
open scoped Classical InnerProductSpace
namespace FreeProbability.Fock
variable {I : Type*} [Fintype I]

/-- All actual words of length at most L, including the empty word. -/
def depthWords (L : ℕ) : Finset (List I) :=
  (Finset.range (L + 1)).biUnion fun n => Finset.univ.image (List.ofFn : (Fin n → I) → List I)

@[simp] theorem mem_depthWords (L : ℕ) (w : List I) : w ∈ depthWords L ↔ w.length ≤ L := by
  constructor
  · intro hw
    obtain ⟨n, hn, hnw⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hnw
    have hh : w.length = n := by rw [← ha, List.length_ofFn]
    rw [hh]
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  · intro hw
    apply Finset.mem_biUnion.mpr
    refine ⟨w.length, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hw), ?_⟩
    exact Finset.mem_image.mpr ⟨w.get, Finset.mem_univ _, List.ofFn_get w⟩

/-- Literal finite-coordinate orthogonal projection onto words of depth at most L. -/
def depthProjection (L : ℕ) : WordSpace I →L[ℂ] WordSpace I := finiteWordProjection (depthWords L)

@[simp] theorem depthProjection_apply (L : ℕ) (f : WordSpace I) (w : List I) :
    depthProjection L f w = if w.length ≤ L then f w else 0 := by
  simp [depthProjection, finiteWordProjection_apply]

@[simp] theorem depthProjection_word (L : ℕ) (w : List I) :
    depthProjection L (word w) = if w.length ≤ L then word w else 0 := by
  by_cases hw : w.length ≤ L
  · rw [ite_eq_left hw]
    apply lp.ext
    funext v
    by_cases hv : v = w
    · subst v; simp [depthProjection_apply, word, lp.single_apply, hw]
    · simp [depthProjection_apply, word, lp.single_apply, hv]
  · rw [ite_eq_right hw]
    apply lp.ext
    funext v
    by_cases hv : v = w
    · subst v; simp [depthProjection_apply, word, hw]
    · simp [depthProjection_apply, word, lp.single_apply, hv]

@[simp] theorem depthProjection_vacuum (L : ℕ) :
    depthProjection L (vacuum : WordSpace I) = vacuum := by
  simpa only [vacuum, List.length_nil, Nat.zero_le, ite_true] using depthProjection_word L ([] : List I)

theorem norm_depthProjection_le (L : ℕ) : ‖depthProjection (I := I) L‖ ≤ 1 :=
  norm_finiteWordProjection_le _

@[simp] theorem depthProjection_adjoint (L : ℕ) :
    (depthProjection (I := I) L).adjoint = depthProjection L := finiteWordProjection_adjoint _

@[simp] theorem depthProjection_idempotent (L : ℕ) :
    (depthProjection (I := I) L).comp (depthProjection L) = depthProjection L :=
  finiteWordProjection_idempotent _

theorem depthProjection_range (L : ℕ) :
    LinearMap.range (depthProjection (I := I) L).toLinearMap =
      Submodule.span ℂ (word '' (depthWords (I := I) L : Set (List I))) := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    exact finiteWordProjection_mem_span _ f
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨word w, ?_⟩
    change depthProjection L (word w) = word w
    rw [depthProjection_word, ite_eq_left ((mem_depthWords L w).mp hw)]

/-- The actual retained range is finite dimensional, rather than an abstract approximation parameter. -/
theorem depthProjection_finiteDimensional (L : ℕ) :
    FiniteDimensional ℂ (LinearMap.range (depthProjection (I := I) L).toLinearMap) := by
  rw [depthProjection_range]
  exact finiteWordProjection_finite_span _

theorem tendsto_depthWords : Filter.Tendsto (depthWords (I := I)) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.mpr
  intro S
  refine Filter.eventually_atTop.mpr ⟨S.sup List.length, ?_⟩
  intro L hL w hw
  exact (mem_depthWords L w).mpr ((Finset.le_sup (f := List.length) hw).trans hL)

/-- Actual finite-depth projections converge in Hilbert norm on every completed Fock vector. -/
theorem tendsto_depthProjection (f : WordSpace I) :
    Filter.Tendsto (fun L => depthProjection L f) Filter.atTop (nhds f) := by
  exact (finiteWordProjection_tendsto f).comp tendsto_depthWords

end FreeProbability.Fock
