import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The Hilbert word model of full Fock space

`WordSpace I` is the completed full Fock space over the one-particle space
`ℓ²(I, ℂ)`, realized as square-summable coefficients of finite words.  This
module constructs creation for the canonical orthonormal one-particle vectors.
Identification with completed tensor powers of an arbitrary Hilbert space is a
separate obligation.  No traciality of the vacuum on all bounded operators is
asserted.
-/

noncomputable section
open scoped ComplexConjugate InnerProductSpace ENNReal Classical

namespace FreeProbability.Fock

variable {I : Type*}

/-- Square-summable complex coefficients on all finite words, including the empty word. -/
abbrev WordSpace (I : Type*) := lp (fun _ : List I => ℂ) 2

/-- The canonical word vector. -/
def word (w : List I) : WordSpace I := by
  classical
  exact lp.single 2 w 1

/-- The empty word is the vacuum. -/
def vacuum : WordSpace I := word []

@[simp] theorem norm_word (w : List I) : ‖word w‖ = 1 := by
  classical
  simp [word, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

@[simp] theorem norm_vacuum : ‖(vacuum : WordSpace I)‖ = 1 := norm_word []

@[simp] theorem inner_word (u v : List I) :
    inner ℂ (word u) (word v) = if u = v then 1 else 0 := by
  classical
  simp [word, lp.inner_single_left, lp.single_apply, Pi.single_apply]

/-- The word vectors are an orthonormal family. -/
theorem orthonormal_word : Orthonormal ℂ (word : List I → WordSpace I) := by
  classical
  rw [orthonormal_iff_ite]
  exact inner_word

private theorem orthonormal_prefix (i : I) :
    Orthonormal ℂ (fun w : List I => word (i :: w)) := by
  classical
  rw [orthonormal_iff_ite]
  intro u v
  simp

/-- Creation by a canonical basis vector is an isometric shift of words. -/
def creationIsometry (i : I) : WordSpace I →ₗᵢ[ℂ] WordSpace I :=
  (orthonormal_prefix i).orthogonalFamily.linearIsometry

/-- The bounded left creation operator. -/
def creation (i : I) : WordSpace I →L[ℂ] WordSpace I :=
  (creationIsometry i).toContinuousLinearMap

@[simp] theorem creation_word (i : I) (w : List I) :
    creation i (word w) = word (i :: w) := by
  classical
  change (orthonormal_prefix i).orthogonalFamily.linearIsometry (lp.single 2 w 1) = _
  rw [OrthogonalFamily.linearIsometry_apply_single]
  simp [LinearIsometry.toSpanSingleton_apply]

@[simp] theorem norm_creation_apply (i : I) (f : WordSpace I) :
    ‖creation i f‖ = ‖f‖ := (creationIsometry i).norm_map f

/-- Annihilation is the Hilbert adjoint of creation. -/
def annihilation (i : I) : WordSpace I →L[ℂ] WordSpace I :=
  (creation i).adjoint

@[simp] theorem inner_word_left (w : List I) (f : WordSpace I) :
    inner ℂ (word w) f = f w := by
  classical
  simp [word, lp.inner_single_left]

@[simp] theorem annihilation_word (i : I) (w : List I) :
    annihilation i (word w) =
      match w with
      | [] => 0
      | j :: v => if i = j then word v else 0 := by
  classical
  ext v
  rw [← inner_word_left, annihilation, ContinuousLinearMap.adjoint_inner_right,
    creation_word, inner_word]
  cases w with
  | nil => simp
  | cons j w => by_cases h : i = j <;> simp [h, word, lp.single_apply, Pi.single_apply]

@[simp] theorem annihilation_vacuum (i : I) :
    annihilation i (vacuum : WordSpace I) = 0 := annihilation_word i []

/-- The canonical self-adjoint semicircular candidate. Its full law is proved separately. -/
def semicircular (i : I) : WordSpace I →L[ℂ] WordSpace I :=
  creation i + annihilation i

/-- The canonical creation/annihilation relation, as an identity of bounded operators. -/
theorem annihilation_creation (i j : I) :
    (annihilation i).comp (creation j) =
      if i = j then ContinuousLinearMap.id ℂ (WordSpace I) else 0 := by
  classical
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  have hz : lp.single (E := fun _ : List I => ℂ) 2 w z = z • word w := by
    simp [word, ← lp.single_smul]
  simp only [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply, hz,
    map_smul, creation_word, annihilation_word]
  by_cases h : i = j <;> simp [h]

@[simp] theorem adjoint_semicircular (i : I) :
    (semicircular i).adjoint = semicircular i := by
  simp [semicircular, annihilation, map_add, ContinuousLinearMap.adjoint_adjoint,
    add_comm]

/-- Evaluation in the vacuum vector; positivity follows from Hilbert-space positivity. -/
def vacuumExpectation (T : WordSpace I →L[ℂ] WordSpace I) : ℂ :=
  inner ℂ (vacuum : WordSpace I) (T vacuum)

@[simp] theorem semicircular_vacuum (i : I) :
    semicircular i (vacuum : WordSpace I) = word [i] := by
  simp [semicircular, vacuum]

@[simp] theorem vacuumExpectation_semicircular (i : I) :
    vacuumExpectation (semicircular i) = 0 := by
  change inner ℂ vacuum (semicircular i vacuum) = 0
  rw [semicircular_vacuum]
  simp only [vacuum, inner_word]
  simp

/-- Covariance of the actual bounded operators, without a freeness assumption. -/
theorem vacuumExpectation_semicircular_comp (i j : I) :
    vacuumExpectation ((semicircular i).comp (semicircular j)) =
      if i = j then 1 else 0 := by
  classical
  unfold vacuumExpectation
  rw [ContinuousLinearMap.comp_apply, semicircular_vacuum]
  simp only [semicircular, add_apply, creation_word, annihilation_word]
  by_cases h : i = j <;> simp [h, vacuum, inner_add_right, word, lp.inner_single_left, lp.single_apply]

end FreeProbability.Fock

