import FreeProbability.Fock.SemicircularNorm
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# The generated faithful tracial C-star probability model

All structure is inherited from the concrete bounded operators and norm closure.
The basis generators have norm two, are self-adjoint, centered and of variance
one. Freeness and the full joint Wick law are proved in `FreeCStarModel` and
`WickFormula`; the semicircular spectral measure remains an analytic obligation.
-/

noncomputable section
open scoped Classical

namespace FreeProbability.Fock

instance (I : Type*) : IsClosed
    (closedSemicircularAlgebra I : Set (WordSpace I →L[ℂ] WordSpace I)) :=
  (semicircularAlgebra I).isClosed_topologicalClosure

/-- The closed generated algebra inherits its C-star algebra structure. -/
example (I : Type*) : CStarAlgebra (closedSemicircularAlgebra I) := inferInstance

/-- The polynomial vacuum state satisfies the project's traciality interface. -/
theorem generatedVacuumState_isTracial (I : Type*) :
    IsTracial (generatedVacuumState I).toProbabilitySpace := by
  intro T U
  exact vacuumExpectation_mul_comm_on_semicircularAlgebra T.property U.property

/-- The closed vacuum state satisfies the project's traciality interface. -/
theorem closedGeneratedVacuumState_isTracial (I : Type*) :
    IsTracial (closedGeneratedVacuumState I).toProbabilitySpace :=
  closedGeneratedVacuumState_tracial I

variable {I : Type*}

/-- A canonical self-adjoint generator inside the actual closed C-star algebra. -/
def closedSemicircular (i : I) : closedSemicircularAlgebra I :=
  ⟨semicircular i, (semicircularAlgebra I).le_topologicalClosure (semicircular_mem_algebra i)⟩

@[simp] theorem coe_closedSemicircular (i : I) :
    (closedSemicircular i : WordSpace I →L[ℂ] WordSpace I) = semicircular i := rfl

@[simp] theorem norm_closedSemicircular (i : I) : ‖closedSemicircular i‖ = 2 :=
  norm_semicircular i

/-- Self-adjointness in the generated algebra itself. -/
theorem isSelfAdjoint_closedSemicircular (i : I) : IsSelfAdjoint (closedSemicircular i) := by
  apply Subtype.ext
  exact (isSelfAdjoint_semicircular i).star_eq

@[simp] theorem closedGeneratedVacuumState_centered (i : I) :
    (closedGeneratedVacuumState I).expectation (closedSemicircular i) = 0 :=
  vacuumExpectation_semicircular i

@[simp] theorem closedGeneratedVacuumState_variance_one (i : I) :
    (closedGeneratedVacuumState I).expectation (closedSemicircular i ^ 2) = 1 :=
  vacuumState_semicircular_sq i

end FreeProbability.Fock
