import FreeProbability.Fock.SecondQuantizationCompressionCP
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! # Actual real rotations of doubled complex Hilbert space -/
noncomputable section
open scoped InnerProductSpace

namespace FreeProbability.Fock
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The genuine Hilbert direct sum; its norm is the L² norm. -/
abbrev DoubledHilbert := WithLp 2 (H × H)

/-- The first coordinate is an actual Hilbert isometry. -/
def doubledFirst : H →ₗᵢ[ℂ] DoubledHilbert H where
  toFun h := WithLp.toLp 2 (h, 0)
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext <;> simp
  map_smul' c h := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext <;> simp
  norm_map' h := WithLp.norm_toLp_fst 2 H H h

/-- The second coordinate is an actual Hilbert isometry. -/
def doubledSecond : H →ₗᵢ[ℂ] DoubledHilbert H where
  toFun h := WithLp.toLp 2 (0, h)
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext <;> simp
  map_smul' c h := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext <;> simp
  norm_map' h := WithLp.norm_toLp_snd 2 H H h

variable {H}

/-- Literal real-coefficient rotation, complex linear on the doubled Hilbert space. -/
def doubledRotationLinear (r s : ℝ) : DoubledHilbert H →ₗ[ℂ] DoubledHilbert H where
  toFun x := WithLp.toLp 2
    ((r : ℂ) • x.fst - (s : ℂ) • x.snd, (s : ℂ) • x.fst + (r : ℂ) • x.snd)
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext <;> simp <;> module
  map_smul' c x := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext <;> simp <;> module

/-- The inverse rotation is the same real cosine and opposite real sine. -/
theorem doubledRotationLinear_inverse (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1)
    (x : DoubledHilbert H) :
    doubledRotationLinear r (-s) (doubledRotationLinear r s x) = x := by
  have hc : (r : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hrs
  have hrr : (r : ℂ) * r + (s : ℂ) * s = 1 := by simpa only [pow_two] using hc
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change (r : ℂ) • ((r : ℂ) • x.fst - (s : ℂ) • x.snd) -
      ((-s : ℝ) : ℂ) • ((s : ℂ) • x.fst + (r : ℂ) • x.snd) = x.fst
    calc
      _ = ((r : ℂ) * r + (s : ℂ) * s) • x.fst := by simp only [Complex.ofReal_neg]; module
      _ = _ := by rw [hrr, one_smul]
  · change ((-s : ℝ) : ℂ) • ((r : ℂ) • x.fst - (s : ℂ) • x.snd) +
      (r : ℂ) • ((s : ℂ) • x.fst + (r : ℂ) • x.snd) = x.snd
    calc
      _ = ((r : ℂ) * r + (s : ℂ) * s) • x.snd := by simp only [Complex.ofReal_neg]; module
      _ = _ := by rw [hrr, one_smul]

/-- The real rotation preserves the actual Hilbert inner product. -/
theorem doubledRotationLinear_inner (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1)
    (x y : DoubledHilbert H) :
    inner ℂ (doubledRotationLinear r s x) (doubledRotationLinear r s y) = inner ℂ x y := by
  have hc : (r : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hrs
  simp only [doubledRotationLinear, LinearMap.coe_mk, AddHom.coe_mk,
    WithLp.prod_inner_apply, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  calc
    _ = ((r : ℂ) ^ 2 + (s : ℂ) ^ 2) * (inner ℂ x.fst y.fst + inner ℂ x.snd y.snd) := by ring
    _ = _ := by rw [hc, one_mul]; rfl

/-- Actual surjective unitary rotation, with genuine inverse, on arbitrary doubled H. -/
def doubledRotation (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) :
    DoubledHilbert H ≃ₗᵢ[ℂ] DoubledHilbert H :=
  LinearEquiv.isometryOfInner
    { toLinearMap := doubledRotationLinear r s
      invFun := doubledRotationLinear r (-s)
      left_inv := doubledRotationLinear_inverse r s hrs
      right_inv := by
        intro x
        have hneg : r ^ 2 + (-s) ^ 2 = 1 := by simpa using hrs
        have hi := doubledRotationLinear_inverse (H := H) r (-s) hneg x
        simp only [neg_neg] at hi
        exact hi }
    (doubledRotationLinear_inner r s hrs)

/-- The rotation of the first-coordinate vector is the literal real linear combination. -/
theorem doubledRotation_first (r s : ℝ) (hrs : r ^ 2 + s ^ 2 = 1) (h : H) :
    doubledRotation r s hrs (doubledFirst H h) =
      (r : ℂ) • doubledFirst H h + (s : ℂ) • doubledSecond H h := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext <;> simp [doubledRotation, doubledRotationLinear, doubledFirst, doubledSecond]

end FreeProbability.Fock
