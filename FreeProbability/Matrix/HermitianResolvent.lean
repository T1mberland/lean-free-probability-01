import FreeProbability.Matrix.RankOneSecular
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Order.Star.Real

/-!
# Exterior resolvents of real Hermitian matrices

The norm in this module is explicitly the Euclidean operator norm. Spectral
diagonalization supplies the resolvent and its quadratic form, with the exterior
domain recorded in each statement.
-/

namespace FreeProbability

open Matrix Unitary
open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n ℝ}

theorem hermitian_norm_eq_eigenvalue_norm (hA : A.IsHermitian) :
    ‖A‖ = ‖hA.eigenvalues‖ := by
  conv_lhs => rw [hA.spectral_theorem, conjStarAlgAut_apply]
  simp [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]

theorem hermitian_eigenvalue_le_norm (hA : A.IsHermitian) (i : n) :
    hA.eigenvalues i ≤ ‖A‖ := by
  rw [hermitian_norm_eq_eigenvalue_norm hA]
  exact (Real.le_norm_self _).trans (norm_le_pi_norm _ i)

theorem hermitian_trace_sq_le_card_mul_norm_sq (hA : A.IsHermitian) :
    (A * A).trace ≤ (Fintype.card n : ℝ) * ‖A‖ ^ 2 := by
  let e := conjStarAlgAut ℝ (Matrix n n ℝ) hA.eigenvectorUnitary
  have hs : A = e (diagonal hA.eigenvalues) := by simpa [e] using hA.spectral_theorem
  have hsq : A * A = e (diagonal (fun i => hA.eigenvalues i ^ 2)) := by
    calc
      _ = e (diagonal hA.eigenvalues) * e (diagonal hA.eigenvalues) := congrArg (fun B => B * B) hs
      _ = _ := by rw [← map_mul, diagonal_mul_diagonal]; simp only [pow_two]
  rw [hsq]
  change ((hA.eigenvectorUnitary : Matrix n n ℝ) * diagonal (fun i => hA.eigenvalues i ^ 2) *
    star (hA.eigenvectorUnitary : Matrix n n ℝ)).trace ≤ _
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]
  calc
    _ ≤ ∑ _i : n, ‖A‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hi : ‖hA.eigenvalues i‖ ≤ ‖A‖ := by
        rw [hermitian_norm_eq_eigenvalue_norm hA]
        exact norm_le_pi_norm _ i
      have hsqle := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hi
      simpa [Real.norm_eq_abs] using hsqle
    _ = _ := by simp [nsmul_eq_mul]

theorem matrixEigenvalue_norm_le {B : Matrix n n ℝ} {z : ℝ}
    (hz : IsMatrixEigenvalue B z) : ‖z‖ ≤ ‖B‖ := by
  obtain ⟨x, hx, he⟩ := hz
  have hv : 0 < ‖WithLp.toLp 2 x‖ := norm_pos_iff.mpr (by simpa using hx)
  have h := Matrix.l2_opNorm_mulVec B (WithLp.toLp 2 x)
  change ‖WithLp.toLp 2 (B *ᵥ x)‖ ≤ ‖B‖ * ‖WithLp.toLp 2 x‖ at h
  rw [he, WithLp.toLp_smul, norm_smul] at h
  exact (mul_le_mul_iff_of_pos_right hv).mp h

/-- Extending a real Hermitian matrix by a zero block preserves its operator norm. -/
theorem hermitian_norm_zero_extension {m : Type*} [Fintype m] [DecidableEq m]
    (hA : A.IsHermitian) :
    ‖fromBlocks A 0 0 (0 : Matrix m m ℝ)‖ = ‖A‖ := by
  let V := hA.eigenvectorUnitary
  have hV : (V : Matrix n n ℝ) * (V : Matrix n n ℝ)ᵀ = 1 := by
    simpa [star_eq_conjTranspose] using Unitary.coe_mul_star_self V
  have hU : fromBlocks (V : Matrix n n ℝ) 0 0 (1 : Matrix m m ℝ) ∈
      Matrix.unitaryGroup (n ⊕ m) ℝ := by
    apply Matrix.mem_unitaryGroup_iff.mpr
    rw [star_eq_conjTranspose, fromBlocks_conjTranspose, fromBlocks_multiply]
    simp [hV, fromBlocks_one]
  let U : Matrix.unitaryGroup (n ⊕ m) ℝ := ⟨_, hU⟩
  have hs : fromBlocks A 0 0 (0 : Matrix m m ℝ) =
      (U : Matrix (n ⊕ m) (n ⊕ m) ℝ) * diagonal (Sum.elim hA.eigenvalues (0 : m → ℝ)) *
        star (U : Matrix (n ⊕ m) (n ⊕ m) ℝ) := by
    have ha : A = (V : Matrix n n ℝ) * diagonal hA.eigenvalues * star (V : Matrix n n ℝ) := by
      simpa [V, conjStarAlgAut_apply] using hA.spectral_theorem
    change _ = fromBlocks (V : Matrix n n ℝ) 0 0 (1 : Matrix m m ℝ) * _ *
      star (fromBlocks (V : Matrix n n ℝ) 0 0 (1 : Matrix m m ℝ))
    rw [← fromBlocks_diagonal, star_eq_conjTranspose, fromBlocks_conjTranspose,
      fromBlocks_multiply, fromBlocks_multiply]
    simpa [star_eq_conjTranspose] using congrArg
      (fun B => fromBlocks B 0 0 (0 : Matrix m m ℝ)) ha
  have hn : ‖Sum.elim hA.eigenvalues (0 : m → ℝ)‖ = ‖hA.eigenvalues‖ := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro i
      cases i with
      | inl i => exact norm_le_pi_norm hA.eigenvalues i
      | inr i => simp
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro i
      exact norm_le_pi_norm (Sum.elim hA.eigenvalues (0 : m → ℝ)) (Sum.inl i)
  rw [hs]
  simpa [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal, hn] using
    (hermitian_norm_eq_eigenvalue_norm hA).symm

theorem hermitian_shift_eq (hA : A.IsHermitian) (z : ℝ) : z • (1 : Matrix n n ℝ) - A =
    conjStarAlgAut ℝ _ hA.eigenvectorUnitary (diagonal (fun i => z - hA.eigenvalues i)) := by
  have he : diagonal (fun i => z - hA.eigenvalues i) =
      z • (1 : Matrix n n ℝ) - diagonal hA.eigenvalues := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [he, map_sub, map_smul, map_one]
  have ha := hA.spectral_theorem
  simpa [Function.comp_def] using congrArg (z • (1 : Matrix n n ℝ) - ·) ha

theorem hermitian_resolvent_eq (hA : A.IsHermitian) (z : ℝ)
    (hz : ∀ i, hA.eigenvalues i < z) :
    (z • (1 : Matrix n n ℝ) - A)⁻¹ =
      conjStarAlgAut ℝ _ hA.eigenvectorUnitary (diagonal (fun i => (z - hA.eigenvalues i)⁻¹)) := by
  have hd : ∀ i, z - hA.eigenvalues i ≠ 0 := fun i => (sub_pos.mpr (hz i)).ne'
  apply Matrix.inv_eq_right_inv
  rw [hermitian_shift_eq hA z, ← map_mul, diagonal_mul_diagonal]
  have he : (fun i => (z - hA.eigenvalues i) * (z - hA.eigenvalues i)⁻¹) = (1 : n → ℝ) := by
    ext i
    exact mul_inv_cancel₀ (hd i)
  simp [he]

theorem hermitian_shift_posDef (hA : A.IsHermitian) (z : ℝ)
    (hz : ∀ i, hA.eigenvalues i < z) : (z • (1 : Matrix n n ℝ) - A).PosDef := by
  rw [hermitian_shift_eq hA z, conjStarAlgAut_apply]
  apply (Matrix.IsUnit.posDef_star_right_conjugate_iff Unitary.isUnit_coe).mpr
  exact posDef_diagonal_iff.mpr (fun i => sub_pos.mpr (hz i))

theorem hermitian_shift_posSemidef (hA : A.IsHermitian) (z : ℝ)
    (hz : ∀ i, hA.eigenvalues i ≤ z) : (z • (1 : Matrix n n ℝ) - A).PosSemidef := by
  rw [hermitian_shift_eq hA z, conjStarAlgAut_apply]
  apply (Matrix.IsUnit.posSemidef_star_right_conjugate_iff Unitary.isUnit_coe).mpr
  exact posSemidef_diagonal_iff.mpr (fun i => sub_nonneg.mpr (hz i))

theorem hermitian_resolvent_det_ne_zero (hA : A.IsHermitian) (z : ℝ)
    (hz : ∀ i, hA.eigenvalues i < z) : (z • (1 : Matrix n n ℝ) - A).det ≠ 0 := by
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (hermitian_shift_posDef hA z hz).isUnit)

/-- The squared coordinates in an orthogonal eigenbasis are nonnegative weights. -/
theorem hermitian_resolvent_form_eq (hA : A.IsHermitian) (u : n → ℝ) (z : ℝ)
    (hz : ∀ i, hA.eigenvalues i < z) :
    u ⬝ᵥ (z • (1 : Matrix n n ℝ) - A)⁻¹ *ᵥ u =
      ∑ i, ((star (hA.eigenvectorUnitary : Matrix n n ℝ)) *ᵥ u) i ^ 2 /
        (z - hA.eigenvalues i) := by
  rw [hermitian_resolvent_eq hA z hz, conjStarAlgAut_apply,
    ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
  have he : u ᵥ* (hA.eigenvectorUnitary : Matrix n n ℝ) =
      star (hA.eigenvectorUnitary : Matrix n n ℝ) *ᵥ u := by
    simpa [star_eq_conjTranspose] using (vecMul_transpose (hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ u)
  rw [he]
  simp only [mulVec_diagonal, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  simp only [div_eq_mul_inv, pow_two]
  ring

noncomputable def realResolventForm (A : Matrix n n ℝ) (u : n → ℝ) (z : ℝ) : ℝ :=
  u ⬝ᵥ (z • (1 : Matrix n n ℝ) - A)⁻¹ *ᵥ u

theorem realResolventForm_nonneg (hA : A.IsHermitian) (u : n → ℝ) (z : ℝ)
    (hz : ∀ i, hA.eigenvalues i < z) : 0 ≤ realResolventForm A u z := by
  rw [realResolventForm, hermitian_resolvent_form_eq hA u z hz]
  exact Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (sub_pos.mpr (hz i)).le)

/-- Exterior resolvent forms decrease as the real parameter increases. -/
theorem realResolventForm_antitone (hA : A.IsHermitian) (u : n → ℝ) (z t : ℝ)
    (hz : ∀ i, hA.eigenvalues i < z) (hzt : z ≤ t) :
    realResolventForm A u t ≤ realResolventForm A u z := by
  rw [realResolventForm, realResolventForm,
    hermitian_resolvent_form_eq hA u t (fun i => (hz i).trans_le hzt),
    hermitian_resolvent_form_eq hA u z hz]
  exact Finset.sum_le_sum (fun i _ => div_le_div_of_nonneg_left (sq_nonneg _)
    (sub_pos.mpr (hz i)) (sub_le_sub_right hzt _))

theorem realResolventForm_strict_antitone (hA : A.IsHermitian) (u : n → ℝ)
    (hu : u ≠ 0) (z t : ℝ) (hz : ∀ i, hA.eigenvalues i < z) (hzt : z < t) :
    realResolventForm A u t < realResolventForm A u z := by
  have hi : Function.Injective (star (hA.eigenvectorUnitary : Matrix n n ℝ)).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr Unitary.isUnit_coe.star
  have hv : star (hA.eigenvectorUnitary : Matrix n n ℝ) *ᵥ u ≠ 0 := by
    intro h
    apply hu
    apply hi
    simpa using h
  obtain ⟨i, hvi⟩ := Function.ne_iff.mp hv
  rw [realResolventForm, realResolventForm,
    hermitian_resolvent_form_eq hA u t (fun j => (hz j).trans hzt),
    hermitian_resolvent_form_eq hA u z hz]
  apply Finset.sum_lt_sum
  · intro j _
    exact div_le_div_of_nonneg_left (sq_nonneg _) (sub_pos.mpr (hz j))
      (sub_le_sub_right hzt.le _)
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    exact div_lt_div_of_pos_left (sq_pos_of_ne_zero hvi) (sub_pos.mpr (hz i))
      (sub_lt_sub_right hzt _)

theorem realResolventForm_strictAntiOn (hA : A.IsHermitian) (u : n → ℝ) (hu : u ≠ 0) :
    StrictAntiOn (realResolventForm A u) (Set.Ioi ‖A‖) := by
  intro z hz t _ hzt
  exact realResolventForm_strict_antitone hA u hu z t
    (fun i => (hermitian_eigenvalue_le_norm hA i).trans_lt hz) hzt

theorem posSemidef_exists_eigenvalue_eq_norm [Nonempty n] (hA : A.PosSemidef) :
    ∃ i, hA.isHermitian.eigenvalues i = ‖A‖ := by
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ hA.isHermitian.eigenvalues
    Finset.univ_nonempty
  refine ⟨i, le_antisymm (hermitian_eigenvalue_le_norm hA.isHermitian i) ?_⟩
  rw [hermitian_norm_eq_eigenvalue_norm hA.isHermitian]
  apply (pi_norm_le_iff_of_nonneg (hA.eigenvalues_nonneg i)).mpr
  intro j
  rw [Real.norm_of_nonneg (hA.eigenvalues_nonneg j)]
  exact hmax j (Finset.mem_univ _)

theorem posSemidef_norm_isEigenvalue [Nonempty n] (hA : A.PosSemidef) :
    IsMatrixEigenvalue A ‖A‖ := by
  obtain ⟨i, hi⟩ := posSemidef_exists_eigenvalue_eq_norm hA
  refine ⟨⇑(hA.isHermitian.eigenvectorBasis i), ?_, ?_⟩
  · exact (WithLp.ofLp_eq_zero 2).ne.mpr (hA.isHermitian.eigenvectorBasis.orthonormal.ne_zero i)
  · rw [hA.isHermitian.mulVec_eigenvectorBasis, hi]

theorem real_quadraticForm_le_operatorNorm (B : Matrix n n ℝ) (x : n → ℝ) :
    x ⬝ᵥ B *ᵥ x ≤ ‖B‖ * ‖WithLp.toLp 2 x‖ ^ 2 := by
  have hi := real_inner_le_norm (WithLp.toLp 2 x) (WithLp.toLp 2 (B *ᵥ x))
  have ho := Matrix.l2_opNorm_mulVec B (WithLp.toLp 2 x)
  change ‖WithLp.toLp 2 (B *ᵥ x)‖ ≤ ‖B‖ * ‖WithLp.toLp 2 x‖ at ho
  calc
    _ ≤ ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 (B *ᵥ x)‖ := by
      simpa [EuclideanSpace.inner_toLp_toLp, dotProduct_comm] using hi
    _ ≤ ‖WithLp.toLp 2 x‖ * (‖B‖ * ‖WithLp.toLp 2 x‖) :=
      mul_le_mul_of_nonneg_left ho (norm_nonneg _)
    _ = _ := by ring

/-- Positivity order implies operator-norm order for real positive matrices. -/
theorem posSemidef_norm_mono [Nonempty n] (hA : A.PosSemidef) (B : Matrix n n ℝ)
    (hBA : (B - A).PosSemidef) : ‖A‖ ≤ ‖B‖ := by
  obtain ⟨i, hi⟩ := posSemidef_exists_eigenvalue_eq_norm hA
  let v := hA.isHermitian.eigenvectorBasis i
  have hv : ‖v‖ = 1 := hA.isHermitian.eigenvectorBasis.orthonormal.1 i
  have hvec : A *ᵥ ⇑v = ‖A‖ • ⇑v := by
    simpa [v, hi] using hA.isHermitian.mulVec_eigenvectorBasis i
  have hdot : ⇑v ⬝ᵥ ⇑v = 1 := by
    have hinner : inner ℝ v v = 1 := by simp [hv]
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using hinner
  have hAv : ⇑v ⬝ᵥ A *ᵥ ⇑v = ‖A‖ := by
    rw [hvec, dotProduct_smul]
    simp [hdot]
  have hnonneg := hBA.dotProduct_mulVec_nonneg ⇑v
  have hlower : ‖A‖ ≤ ⇑v ⬝ᵥ B *ᵥ ⇑v := by
    simpa [Matrix.sub_mulVec, dotProduct_sub, hAv] using hnonneg
  have hupper := real_quadraticForm_le_operatorNorm B ⇑v
  have hnorm : ‖WithLp.toLp 2 ⇑v‖ = 1 := hv
  simpa [hnorm] using hlower.trans hupper

/-- A secular value at most one bounds the norm of a positive rank-one update.
The norm is the Euclidean operator norm throughout this statement. -/
theorem rankOne_norm_le_of_resolvent_le [Nonempty n] (hA : A.PosSemidef) (u : n → ℝ)
    (z : ℝ) (hz : ‖A‖ < z) (hform : realResolventForm A u z ≤ 1) :
    ‖A + vecMulVec u u‖ ≤ z := by
  by_cases hu : u = 0
  · subst u
    simpa using hz.le
  · by_contra hle
    have hzt : z < ‖A + vecMulVec u u‖ := lt_of_not_ge hle
    have hps : (A + vecMulVec u u).PosSemidef :=
      hA.add (by simpa using posSemidef_vecMulVec_self_star u)
    have heig := posSemidef_norm_isEigenvalue hps
    have ht : ∀ i, hA.isHermitian.eigenvalues i < ‖A + vecMulVec u u‖ :=
      fun i => ((hermitian_eigenvalue_le_norm hA.isHermitian i).trans_lt hz).trans hzt
    have hsec := (rankOne_isEigenvalue_iff A u u _
      (hermitian_resolvent_det_ne_zero hA.isHermitian _ ht)).mp heig
    have hvalue : realResolventForm A u ‖A + vecMulVec u u‖ = 1 := by
      unfold secular at hsec
      exact (sub_eq_zero.mp hsec).symm
    have hlt := realResolventForm_strict_antitone hA.isHermitian u hu z _
      (fun i => (hermitian_eigenvalue_le_norm hA.isHermitian i).trans_lt hz) hzt
    linarith

/-- An exterior norm gap forces the rank-one resolvent form above one. -/
theorem rankOne_norm_gap_implies_resolvent_gt_one [Nonempty n] (hA : A.PosSemidef)
    (u : n → ℝ) (z : ℝ) (hz : ‖A‖ < z) (hgap : z < ‖A + vecMulVec u u‖) :
    1 < realResolventForm A u z := by
  by_contra h
  exact (not_le_of_gt hgap) (rankOne_norm_le_of_resolvent_le hA u z hz (le_of_not_gt h))

theorem rankOne_resolvent_le_of_norm_le (hA : A.PosSemidef) (u : n → ℝ)
    (z : ℝ) (hz : ‖A‖ < z) (hbound : ‖A + vecMulVec u u‖ ≤ z) :
    realResolventForm A u z ≤ 1 := by
  let R := (z • (1 : Matrix n n ℝ) - A)⁻¹
  let x := R *ᵥ u
  have hbase := hermitian_resolvent_det_ne_zero hA.isHermitian z
    (fun i => (hermitian_eigenvalue_le_norm hA.isHermitian i).trans_lt hz)
  have hx : (z • (1 : Matrix n n ℝ) - A) *ᵥ x = u := by
    dsimp [x, R]
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hbase), one_mulVec]
  have hps : (A + vecMulVec u u).PosSemidef :=
    hA.add (by simpa using posSemidef_vecMulVec_self_star u)
  have hshift := hermitian_shift_posSemidef hps.isHermitian z
    (fun i => (hermitian_eigenvalue_le_norm hps.isHermitian i).trans hbound)
  have he : z • (1 : Matrix n n ℝ) - (A + vecMulVec u u) =
      (z • (1 : Matrix n n ℝ) - A) - vecMulVec u u := by abel
  have hp := hshift.dotProduct_mulVec_nonneg x
  rw [he, Matrix.sub_mulVec, hx, dotProduct_sub, Matrix.vecMulVec_mulVec,
    dotProduct_smul] at hp
  have hq : x ⬝ᵥ u = realResolventForm A u z := by
    rw [dotProduct_comm]
    rfl
  have hpx : 0 ≤ realResolventForm A u z - realResolventForm A u z ^ 2 := by
    simpa [hq, dotProduct_comm u x, pow_two] using hp
  nlinarith

theorem rankOne_norm_le_iff_resolvent_le [Nonempty n] (hA : A.PosSemidef) (u : n → ℝ)
    (z : ℝ) (hz : ‖A‖ < z) :
    ‖A + vecMulVec u u‖ ≤ z ↔ realResolventForm A u z ≤ 1 :=
  ⟨rankOne_resolvent_le_of_norm_le hA u z hz, rankOne_norm_le_of_resolvent_le hA u z hz⟩

theorem rankOne_norm_lt_iff_resolvent_lt [Nonempty n] (hA : A.PosSemidef) (u : n → ℝ)
    (z : ℝ) (hz : ‖A‖ < z) :
    ‖A + vecMulVec u u‖ < z ↔ realResolventForm A u z < 1 := by
  have hpos : 0 < z := (norm_nonneg _).trans_lt hz
  have hbase := hermitian_resolvent_det_ne_zero hA.isHermitian z
    (fun i => (hermitian_eigenvalue_le_norm hA.isHermitian i).trans_lt hz)
  have hps : (A + vecMulVec u u).PosSemidef :=
    hA.add (by simpa using posSemidef_vecMulVec_self_star u)
  have heq : IsMatrixEigenvalue (A + vecMulVec u u) z ↔ realResolventForm A u z = 1 := by
    rw [rankOne_isEigenvalue_iff _ _ _ _ hbase]
    unfold secular realResolventForm
    rw [sub_eq_zero, eq_comm]
  constructor
  · intro hnorm
    have hle := rankOne_resolvent_le_of_norm_le hA u z hz hnorm.le
    apply lt_of_le_of_ne hle
    intro hform
    have hn := matrixEigenvalue_norm_le (heq.mpr hform)
    rw [Real.norm_of_nonneg hpos.le] at hn
    exact (not_le_of_gt hnorm) hn
  · intro hform
    have hle := rankOne_norm_le_of_resolvent_le hA u z hz hform.le
    apply lt_of_le_of_ne hle
    intro hnorm
    have heig := posSemidef_norm_isEigenvalue hps
    rw [hnorm] at heig
    exact (ne_of_lt hform) (heq.mp heig)

theorem rankOne_exterior_eigenvalues_unique (hA : A.IsHermitian) (u : n → ℝ)
    (z t : ℝ) (hz : ‖A‖ < z) (ht : ‖A‖ < t)
    (hez : IsMatrixEigenvalue (A + vecMulVec u u) z)
    (het : IsMatrixEigenvalue (A + vecMulVec u u) t) : z = t := by
  have hf (s : ℝ) (hs : ‖A‖ < s) (he : IsMatrixEigenvalue (A + vecMulVec u u) s) :
      realResolventForm A u s = 1 := by
    have hsec := (rankOne_isEigenvalue_iff _ _ _ _ (hermitian_resolvent_det_ne_zero hA s
      (fun i => (hermitian_eigenvalue_le_norm hA i).trans_lt hs))).mp he
    exact (sub_eq_zero.mp hsec).symm
  have hfz := hf z hz hez
  have hft := hf t ht het
  have hu : u ≠ 0 := by
    intro hu
    simp [hu, realResolventForm] at hfz
  exact (realResolventForm_strictAntiOn hA u hu).injOn hz ht (hfz.trans hft.symm)

theorem rankOne_eigenvector_eq_resolvent_smul (u : n → ℝ) (z : ℝ)
    (hbase : (z • (1 : Matrix n n ℝ) - A).det ≠ 0) (x : n → ℝ)
    (hx : (A + vecMulVec u u) *ᵥ x = z • x) :
    x = (u ⬝ᵥ x) • ((z • (1 : Matrix n n ℝ) - A)⁻¹ *ᵥ u) := by
  have hs : (z • (1 : Matrix n n ℝ) - A) *ᵥ x = (u ⬝ᵥ x) • u := by
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [← hx]
    simp [Matrix.add_mulVec, Matrix.vecMulVec_mulVec]
  have h := congrArg (fun y => (z • (1 : Matrix n n ℝ) - A)⁻¹ *ᵥ y) hs
  simpa [Matrix.mulVec_mulVec, Matrix.mulVec_smul,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hbase)] using h

/-- All nonzero eigenvectors at an exterior eigenvalue span one line. -/
theorem rankOne_eigenvectors_proportional (u : n → ℝ) (z : ℝ)
    (hbase : (z • (1 : Matrix n n ℝ) - A).det ≠ 0) (x y : n → ℝ) (hy : y ≠ 0)
    (hx : (A + vecMulVec u u) *ᵥ x = z • x)
    (hyz : (A + vecMulVec u u) *ᵥ y = z • y) : ∃ r : ℝ, x = r • y := by
  have hxx := rankOne_eigenvector_eq_resolvent_smul u z hbase x hx
  have hyy := rankOne_eigenvector_eq_resolvent_smul u z hbase y hyz
  have hcoeff : u ⬝ᵥ y ≠ 0 := by
    intro h
    apply hy
    simpa [h] using hyy
  refine ⟨(u ⬝ᵥ x) / (u ⬝ᵥ y), ?_⟩
  calc
    x = (u ⬝ᵥ x) • ((z • (1 : Matrix n n ℝ) - A)⁻¹ *ᵥ u) := hxx
    _ = ((u ⬝ᵥ x) / (u ⬝ᵥ y)) •
        ((u ⬝ᵥ y) • ((z • (1 : Matrix n n ℝ) - A)⁻¹ *ᵥ u)) := by
      rw [smul_smul, div_mul_cancel₀ _ hcoeff]
    _ = _ := congrArg (((u ⬝ᵥ x) / (u ⬝ᵥ y)) • ·) hyy.symm

/-- At most one eigenvalue, counted with multiplicity, can exceed the base norm. -/
theorem rankOne_exterior_eigenvalue_indices_subsingleton (hA : A.IsHermitian) (u : n → ℝ)
    (hB : (A + vecMulVec u u).IsHermitian) :
    Set.Subsingleton {i : n | ‖A‖ < hB.eigenvalues i} := by
  intro i hi j hj
  by_contra hij
  have hne (k : n) : ⇑(hB.eigenvectorBasis k) ≠ (0 : n → ℝ) :=
    (WithLp.ofLp_eq_zero 2).ne.mpr (hB.eigenvectorBasis.orthonormal.ne_zero k)
  have heig (k : n) : IsMatrixEigenvalue (A + vecMulVec u u) (hB.eigenvalues k) :=
    ⟨_, hne k, hB.mulVec_eigenvectorBasis k⟩
  have he := rankOne_exterior_eigenvalues_unique hA u _ _ hi hj (heig i) (heig j)
  have hy : (A + vecMulVec u u) *ᵥ ⇑(hB.eigenvectorBasis j) =
      hB.eigenvalues i • ⇑(hB.eigenvectorBasis j) := by
    rw [he]
    exact hB.mulVec_eigenvectorBasis j
  obtain ⟨r, hr⟩ := rankOne_eigenvectors_proportional u (hB.eigenvalues i)
    (hermitian_resolvent_det_ne_zero hA _
      (fun k => (hermitian_eigenvalue_le_norm hA k).trans_lt hi))
    _ _ (hne j) (hB.mulVec_eigenvectorBasis i) hy
  have hv : hB.eigenvectorBasis i = r • hB.eigenvectorBasis j := by
    simpa using congrArg (WithLp.toLp 2) hr
  have hi0 := hB.eigenvectorBasis.orthonormal.inner_eq_zero hij
  rw [hv, inner_smul_left] at hi0
  have hr0 : r = 0 := by
    simpa [inner_self_eq_norm_sq_to_K, hB.eigenvectorBasis.orthonormal.1 j] using hi0
  have hn := hB.eigenvectorBasis.orthonormal.1 i
  rw [hv, hr0] at hn
  simp at hn

end FreeProbability
