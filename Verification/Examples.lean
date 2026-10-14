import FreeProbability

/-! Small applications of the public interfaces, checked with the audit target. -/

open scoped TensorProduct

namespace FreeProbability.Examples

/-- An odd-order pairing sum is zero for every choice of weights. This is the
combinatorial side of the vanishing of odd moments in a Wick formula. -/
example {n : ℕ} (hn : Odd n) (weight : NoncrossingPairing n → ℂ) :
    ∑ p, weight p = 0 := by
  classical
  let : IsEmpty (NoncrossingPairing n) :=
    ⟨fun p => NoncrossingPairing.not_nonempty_of_odd hn ⟨p⟩⟩
  simp

/-- The adjacent-pair theorem expressed using the public partner map. -/
example {n : ℕ} (p : NoncrossingPairing n) (hn : 0 < n) :
    ∃ i : Fin n, i.val + 1 = (p.partner i).val := by
  obtain ⟨i, j, hij, hrel⟩ := p.property.exists_adjacent hn
  have hji : j ≠ i := by
    intro h
    subst j
    omega
  have hj := (p.rel_iff i j).mp hrel
  exact ⟨i, (hj.resolve_left hji) ▸ hij⟩

/-- The bounded word-Fock operators already yield the fourth moment two by
their explicit vacuum action, without assuming a semicircular distribution. -/
example {I : Type*} (i : I) :
    Fock.vacuumExpectation ((Fock.semicircular i).comp
      ((Fock.semicircular i).comp
        ((Fock.semicircular i).comp (Fock.semicircular i)))) = 2 := by
  classical
  simp [Fock.vacuumExpectation, ContinuousLinearMap.comp_apply, Fock.semicircular,
    Fock.vacuum, inner_add_right]
  norm_num [Fock.word, lp.single_apply]

/-- Distinct ordered two-letter Wick words are orthogonal in the actual state. -/
example {I : Type*} (i j : I) (h : i ≠ j) :
    (Fock.vacuumState I).expectation (star (Fock.wick [i, j]) * Fock.wick [j, i]) = 0 := by
  classical
  simp [Fock.vacuumExpectation_wick_star_mul, h]

/-- Commutators have zero expectation in the closed generated algebra. -/
example {I : Type*} (T U : Fock.closedSemicircularAlgebra I) :
    (Fock.closedGeneratedVacuumState I).expectation (T * U - U * T) = 0 := by
  rw [map_sub, Fock.closedGeneratedVacuumState_tracial I T U, sub_self]

/-- At order three, centering one coordinate leaves the cumulant unchanged. -/
example {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
    (φ : ProbabilitySpace 𝕜 A) (a b c : A) :
    cumulant φ [a, φ.center b, c] = cumulant φ [a, b, c] := by
  simpa using cumulant_update_center φ (by norm_num : 2 ≤ 3)
    (fun i : Fin 3 => ![a, b, c] i) (1 : Fin 3)

/-- A genuinely alternating fourth moment vanishes in the actual faithful
tracial C-star model, including repeated nonadjacent colors. -/
example {I : Type*} (i j : I) (h : i ≠ j) :
    (Fock.closedGeneratedVacuumState I).expectation
      (Fock.closedSemicircular i * Fock.closedSemicircular j *
        Fock.closedSemicircular i * Fock.closedSemicircular j) = 0 := by
  classical
  let w : List (I × Fock.closedSemicircularAlgebra I) :=
    [(i, Fock.closedSemicircular i), (j, Fock.closedSemicircular j),
      (i, Fock.closedSemicircular i), (j, Fock.closedSemicircular j)]
  have hh := Fock.freelyIndependent_closedGeneratedVacuumState I w
    (by simp [w]) (by simp [w, List.isChain_cons_cons, h, Ne.symm h])
    (by
      intro x hx
      simp only [w, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;>
        exact Fock.closedSemicircular_mem_closedGeneratorAlgebra _)
    (by
      intro x hx
      simp only [w, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;>
        exact Fock.closedGeneratedVacuumState_centered _)
  simpa [w, wordProduct, mul_assoc] using hh

/-- Mixed third cumulants vanish without centering, positivity or traciality. -/
example {𝕜 A I : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
    (φ : ProbabilitySpace 𝕜 A) (B : I → Subalgebra 𝕜 A)
    (hf : FreelyIndependent φ B) (i j : I) (hij : i ≠ j)
    (a b c : A) (ha : a ∈ B i) (hb : b ∈ B j) (hc : c ∈ B i) :
    cumulant φ [a, b, c] = 0 := by
  have h := hf.cumulant_ofFn_eq_zero_of_mixed
    (fun k : Fin 3 => ![a, b, c] k) (fun k : Fin 3 => ![i, j, i] k)
    (by intro k; fin_cases k <;> simp [ha, hb, hc])
    ⟨0, 1, by simpa using hij⟩
  simpa using h

/-- The all-order Catalan theorem gives the genuine sixth moment. -/
example {I : Type*} (i : I) :
    (Fock.closedGeneratedVacuumState I).expectation (Fock.closedSemicircular i ^ 6) = 5 := by
  simpa [catalan_three] using Fock.closedGeneratedVacuumState_even i 3

/-- Differentiating a noncommutative repeated-letter word preserves its ordered factors. -/
example {I : Type*} (i j : I) (hij : i ≠ j) :
    freeDifferenceQuotient i (wordMonomial (𝕜 := ℂ) [i, j, i]) =
      (1 : WordPolynomial ℂ I) ⊗ₜ[ℂ] wordMonomial [j, i] +
        wordMonomial [i, j] ⊗ₜ[ℂ] (1 : WordPolynomial ℂ I) := by
  simp [wordDifferenceQuotient, hij, ← wordMonomial_append]

/-- Boxed convolution gives the vanishing ordinary second cumulant of a
product of centered free variables, without a trace or positivity assumption. -/
example {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
    (φ : ProbabilitySpace 𝕜 A) (B : Fin 2 → Subalgebra 𝕜 A)
    (hf : FreelyIndependent φ B) (a b : A) (ha : a ∈ B 0) (hb : b ∈ B 1)
    (hca : φ.expectation a = 0) (hcb : φ.expectation b = 0) :
    cumulant φ [a * b, a * b] = 0 := by
  classical
  have hd (x : A) (hx : φ.expectation x = 0) :
      orderedPartitionContribution (cumulant φ) (fun _ : Fin 2 => x)
        (NoncrossingPartition.discrete 2) = 0 := by
    unfold orderedPartitionContribution
    have hs : ({0} : Finset (Fin 2)) ∈ (NoncrossingPartition.discrete 2).blocks := by
      rw [NoncrossingPartition.blocks_discrete]
      exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
    apply Finset.prod_eq_zero hs
    simp [orderedBlockWord, cumulant, hx]
  calc
    _ = ∑ p : NoncrossingPartition 2,
        orderedPartitionContribution (cumulant φ) (fun _ => a) p *
          orderedPartitionContribution (cumulant φ) (fun _ => b) p.kreweras := by
      simpa using hf.cumulant_replicate_mul_eq_kreweras_sum a b ha hb 2 (by norm_num)
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro p _
      rcases p.two_eq_discrete_or_indiscrete with hp | hp
      · rw [hp, hd a hca, zero_mul]
      · rw [hp, NoncrossingPartition.kreweras_indiscrete, hd b hcb, mul_zero]

/-- Arbitrarily varying canonical generators converge at z = I, inside the
norm-two disk where an exterior geometric-series argument does not apply. -/
example {I : Type*} (i : I) (j : ℕ → I) :
    Filter.Tendsto
      (fun n => (Fock.closedGeneratedVacuumState I).cauchyTransform
        (Fock.closedSemicircular (j n)) Complex.I)
      Filter.atTop
      (nhds ((Fock.closedGeneratedVacuumState I).cauchyTransform
        (Fock.closedSemicircular i) Complex.I)) := by
  let _ : PartialOrder (Fock.closedSemicircularAlgebra I) := CStarAlgebra.spectralOrder _
  let _ : StarOrderedRing (Fock.closedSemicircularAlgebra I) := CStarAlgebra.spectralOrderedRing _
  apply tendsto_cauchyTransform_all_nonreal_of_bounded_power_moments
    (Fock.closedGeneratedVacuumState I) (fun _ : ℕ => Fock.closedGeneratedVacuumState I)
    (Fock.closedSemicircular i) (Fock.isSelfAdjoint_closedSemicircular i)
    (fun n => Fock.closedSemicircular (j n))
    (fun n => Fock.isSelfAdjoint_closedSemicircular (j n)) Filter.atTop
    ?_ 2 ?_ Complex.I (by simp)
  · intro k
    have he (q : I) : (Fock.closedGeneratedVacuumState I).expectation
        (Fock.closedSemicircular q ^ k) =
        if Even k then (catalan (k / 2) : ℂ) else 0 := by
      change Fock.vacuumExpectation
        ((Fock.closedSemicircularAlgebra I).val (Fock.closedSemicircular q ^ k)) = _
      rw [map_pow]
      exact Fock.vacuumExpectation_semicircular_pow q k
    simpa only [he] using
      (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℕ => if Even k then (catalan (k / 2) : ℂ) else 0) Filter.atTop
        (nhds (if Even k then (catalan (k / 2) : ℂ) else 0)))
  · exact Filter.Eventually.of_forall (fun n => by simp)

/-- Both spectral endpoints belong to the spectrum of the actual bounded operator. -/
example {I : Type*} (i : I) :
    (-2 : ℝ) ∈ spectrum ℝ (Fock.semicircular i) ∧
      (2 : ℝ) ∈ spectrum ℝ (Fock.semicircular i) := by
  rw [Fock.spectrum_semicircular_real]
  norm_num

/-- The actual Fock spectral measure has the explicit density's fourth moment. -/
example {I : Type*} (i : I) :
    ∫ x : ℝ, x ^ 4 ∂Fock.fockSpectralLaw i = 2 := by
  rw [Fock.fockSpectralLaw_eq_semicircleMeasure]
  simpa [catalan_two] using Semicircular.semicircleMeasure_even_moment 2

/-- The unique physical branch computes an actual Cauchy value inside the norm-two disk. -/
example {I : Type*} (i : I) :
    (Fock.closedGeneratedVacuumState I).cauchyTransform
      (Fock.closedSemicircular i) ((3 / 2 : ℂ) * Complex.I) =
        -(1 / 2 : ℂ) * Complex.I := by
  symm
  apply Fock.closedSemicircular_cauchyTransform_physical_branch
  · norm_num
  · norm_num [Complex.ext_iff, pow_two, Complex.mul_re, Complex.mul_im]
  · norm_num

/-- Any orthonormal family, including a nonspanning family, has an actual faithful
Fock realization with sixth moment five and the explicit spectral density. -/
example {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {e : I → H} (he : Orthonormal ℂ e) :
    ∃ d : Fock.OrthonormalFamilyExtension e,
      IsFaithful d.state.toProbabilitySpace ∧
      ∀ i, d.state.expectation (d.generator i ^ 6) = 5 ∧
        d.spectralLaw i = Semicircular.semicircleMeasure := by
  obtain ⟨d, hf, _, _, hd⟩ := Fock.exists_fullFock_semicircular_family he
  refine ⟨d, hf, fun i => ⟨?_, (hd i).2.2.2.2.1⟩⟩
  simpa [catalan_three] using d.even_moment i 3

/-- Two noncommuting Hermitian Pauli coefficients give actual matrix covariance 2I. -/
example :
    let C : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
      ![!![1, 0; 0, -1], !![0, 1; 1, 0]]
    matrixExpectation (Fock.closedGeneratedVacuumState (Fin 2)).toProbabilitySpace
      (Fock.closedMatrixSemicircular C ^ 2) = (2 : ℂ) • 1 := by
  intro C
  calc
    _ = matrixCovariance C 1 := by
      simpa only [map_one, mul_one, ← pow_two] using
        Fock.closedMatrixSemicircular_covariance C 1
    _ = _ := by
      ext r c
      fin_cases r <;> fin_cases c <;>
        norm_num [C, matrixCovariance, Matrix.mul_apply, Fin.sum_univ_two]

/-- The actual fourth operator-valued moment retains both noncrossing nestings. -/
example {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n]
    (C : I → Matrix n n ℂ) :
    Fock.closedMatrixMoment C 4 =
      matrixCovariance C 1 * matrixCovariance C 1 +
        matrixCovariance C (matrixCovariance C 1) := by
  have h2 : Fock.closedMatrixMoment C 2 = matrixCovariance C 1 := by
    simpa using Fock.closedMatrixMoment_recursion C 1
  simpa [Finset.sum_range_succ, h2, -matrixCovariance_apply] using
    Fock.closedMatrixMoment_recursion C 3

/-- The half-trace projection's actual law is the equal two-atom probability. -/
example {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (φ : StarProbabilitySpace A) {p : A} (hp : IsSelfAdjoint p)
    (hpi : IsIdempotentElem p) (hα : φ.expectation p = (1 / 2 : ℂ)) :
    spectralMeasure φ hp =
      ENNReal.ofReal (1 / 2 : ℝ) • MeasureTheory.Measure.dirac 0 +
        ENNReal.ofReal (1 / 2 : ℝ) • MeasureTheory.Measure.dirac 1 := by
  rw [spectralMeasure_projection φ hp hpi, hα]
  norm_num

/-- Mixed exponential moments vanish even at a large imaginary parameter,
using the actual norm-convergent operator exponential. -/
example {I : Type*} (i j : I) (hij : i ≠ j) :
    Fock.vacuumExpectation (Fock.semicircular i *
      NormedSpace.exp (((10 : ℂ) * Complex.I) • Fock.semicircular j)) = 0 := by
  rw [Fock.vacuumExpectation_semicircular_mul_semicircular_exp]
  simp [hij]

/-- The actual affine Dyson equation applies to noncommuting Hermitian drift
and random coefficients at z = I, without any exterior-radius premise. -/
example :
    let C₀ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
    let C : Fin 1 → Matrix (Fin 2) (Fin 2) ℂ := fun _ => !![0, 1; 1, 0]
    (Fock.operatorMatrixPencilCauchy C₀ C Complex.I)⁻¹ =
      Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ) - C₀ -
        matrixCovariance C (Fock.operatorMatrixPencilCauchy C₀ C Complex.I) := by
  intro C₀ C
  apply Fock.operatorMatrixPencilCauchy_inverse_dyson_nonreal
  · ext r c
    fin_cases r <;> fin_cases c <;> norm_num [C₀, Matrix.conjTranspose]
  · intro i
    ext r c
    fin_cases r <;> fin_cases c <;> norm_num [C, Matrix.conjTranspose]
  · simp

/-- Resolvent IBP for an ordered two-letter polynomial keeps the right boundary
factor, throughout its actual invertibility domain. -/
example {I : Type*} (i j : I) (hij : i ≠ j) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (evaluate Fock.semicircular (wordMonomial (𝕜 := ℂ) [j, i]))) :
    let R := resolvent (evaluate Fock.semicircular (wordMonomial (𝕜 := ℂ) [j, i])) z
    Fock.vacuumExpectation (Fock.semicircular i * R) =
      Fock.vacuumExpectation (R * Fock.semicircular j) * Fock.vacuumExpectation R := by
  classical
  have hd : freeDifferenceQuotient i (wordMonomial (𝕜 := ℂ) [j, i]) =
      wordMonomial [j] ⊗ₜ[ℂ] (1 : WordPolynomial ℂ I) := by
    unfold wordMonomial
    rw [freeDifferenceQuotient_single]
    simp [wordDifferenceQuotient, hij, wordMonomial, MonoidAlgebra.one_def]
  have he : evaluate Fock.semicircular (wordMonomial (𝕜 := ℂ) [j]) = Fock.semicircular j := by
    simp only [wordMonomial, evaluate_single, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, one_smul, mul_one]
  have h := Fock.vacuumExpectation_polynomial_resolvent_integrationByParts
    i (wordMonomial (𝕜 := ℂ) [j, i]) z hz
  rw [hd, Fock.sandwichPolynomialExpectation_tmul, he, map_one, one_mul] at h
  exact h

/-- A genuine infinite geometric operator series has explicitly verified value
and derivative convergence bounds in the norm-two semicircular model. -/
example {I : Type*} (i : I) :
    Fock.vacuumExpectation (Fock.semicircular i *
      analyticSeries (fun n => (1 / 4 : ℂ) ^ n) (Fock.semicircular i)) =
      ∑' n, (1 / 4 : ℂ) ^ (n + 1) *
        Fock.analyticPolynomialDerivativeTerm i (wordMonomial (𝕜 := ℂ) [i]) n := by
  have he : evaluate Fock.semicircular (wordMonomial (𝕜 := ℂ) [i]) = Fock.semicircular i := by
    simp only [wordMonomial, evaluate_single, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, one_smul, mul_one]
  have hg : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hn : Summable (fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ) ^ n) := by
    simpa [norm_mul, norm_pow] using
      (summable_norm_pow_mul_geometric_of_norm_lt_one 1
        (r := (1 / 2 : ℝ)) (by norm_num))
  have hdg : Summable (fun n : ℕ => (n + 1 : ℝ) * (1 / 2 : ℝ) ^ n) := by
    simpa [add_mul] using hn.add hg
  have hv : Summable (fun n => ‖(1 / 4 : ℂ) ^ n‖ * ‖Fock.semicircular i‖ ^ n) := by
    convert hg using 1
    funext n
    rw [norm_pow, Fock.norm_semicircular, ← mul_pow]
    norm_num
  have hd : Summable (fun n : ℕ => (n + 1 : ℝ) *
      ‖(1 / 4 : ℂ) ^ (n + 1)‖ * ‖Fock.semicircular i‖ ^ n) := by
    convert hdg.mul_left (1 / 4 : ℝ) using 1
    funext n
    rw [norm_pow, Fock.norm_semicircular, pow_succ]
    have ht : ‖(1 / 4 : ℂ)‖ = (1 / 4 : ℝ) := by norm_num
    rw [ht]
    have hr : (1 / 4 : ℝ) ^ n * 2 ^ n = (1 / 2 : ℝ) ^ n := by
      rw [← mul_pow]
      norm_num
    calc
      _ = (1 / 4 : ℝ) * ((n + 1 : ℝ) * ((1 / 4 : ℝ) ^ n * 2 ^ n)) := by ring
      _ = _ := by rw [hr]
  simpa only [he] using
    Fock.vacuumExpectation_polynomial_analyticSeries_integrationByParts
      i (wordMonomial (𝕜 := ℂ) [i]) (fun n => (1 / 4 : ℂ) ^ n)
      (by simpa only [he] using hv) (by simpa only [he] using hd)

-- All three genuine contractions of the degree-two Wick square survive.
example {I : Type*} (i : I) :
    Fock.wick [i, i] * Fock.wick [i, i] =
      Fock.wick [i, i, i, i] + Fock.wick [i, i] + 1 := by
  simpa [Fin.sum_univ_succ, List.IsPrefix, Fock.wick, add_comm] using
    Fock.wick_product_contractions [i, i] [i, i]

-- Strict sign for an actual noncommuting affine pencil at an interior point.
open scoped ComplexOrder in
example :
    let C₀ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
    let C : Fin 1 → Matrix (Fin 2) (Fin 2) ℂ := fun _ => !![0, 1; 1, 0]
    (matrixNegativeImaginaryPart (Fock.operatorMatrixPencilCauchy C₀ C Complex.I)).PosDef := by
  intro C₀ C
  apply Fock.operatorMatrixPencilCauchy_negativeImaginaryPart_posDef
  · ext r c
    fin_cases r <;> fin_cases c <;> norm_num [C₀, Matrix.conjTranspose]
  · intro i
    ext r c
    fin_cases r <;> fin_cases c <;> norm_num [C, Matrix.conjTranspose]
  · simp

-- Every point above the true edge has an exact positive Dyson test matrix,
-- even when the drift and random coefficient do not commute.
open scoped ComplexOrder in
example (x : ℝ) :
    let C₀ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
    let C : Fin 1 → Matrix (Fin 2) (Fin 2) ℂ := fun _ => !![0, 1; 1, 0]
    Fock.operatorMatrixPencilTopEdge C₀ C < x →
      ∃ Z : Matrix (Fin 2) (Fin 2) ℂ, Z.PosDef ∧
        C₀ + Z + C 0 * Z⁻¹ * C 0 = (x : ℂ) • 1 := by
  intro C₀ C hx
  have hC₀ : C₀.IsHermitian := by
    ext r c
    fin_cases r <;> fin_cases c <;> norm_num [C₀, Matrix.conjTranspose]
  have hC : ∀ i, (C i).IsHermitian := by
    intro i
    ext r c
    fin_cases r <;> fin_cases c <;> norm_num [C, Matrix.conjTranspose]
  simpa [matrixCovariance, Fin.sum_univ_succ] using
    Fock.operatorMatrixPencil_variational_witness C₀ C hC₀ hC x hx

-- A singular density tests a genuinely noncommuting two-coefficient pencil.
open scoped ComplexOrder in
example :
    let C₀ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
    let C : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
      ![!![1, 0; 0, -1], !![0, 1; 1, 0]]
    3 ≤ Fock.operatorMatrixPencilTopEdge C₀ C := by
  intro C₀ C
  let ρ : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, 0]
  have hρ : ρ.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num
  have htr : ρ.trace = 1 := by
    norm_num [ρ, Matrix.trace, Fin.sum_univ_succ]
  have hC₀ : C₀.IsHermitian := by
    ext r c
    fin_cases r <;> fin_cases c <;> norm_num [C₀, Matrix.conjTranspose]
  have hC : ∀ i, (C i).IsHermitian := by
    intro i
    fin_cases i <;> ext r c <;> fin_cases r <;> fin_cases c <;>
      norm_num [C, Matrix.conjTranspose]
  have h := Fock.operatorMatrixPencilTopEdge_density_lower ρ hρ htr C₀ C hC₀ hC
  norm_num [ρ, C₀, C, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ] at h
  exact h

-- At one unit above the actual edge, all three order assertions follow
-- without an operator-norm-radius assumption.
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator in
example {I n : Type*} [Fintype I] [Fintype n] [DecidableEq n] [Nonempty n]
    (C₀ : Matrix n n ℂ) (C : I → Matrix n n ℂ)
    (hC₀ : C₀.IsHermitian) (hC : ∀ i, (C i).IsHermitian) :
    let x : ℝ := Fock.operatorMatrixPencilTopEdge C₀ C + 1
    let M := Fock.operatorMatrixPencilCauchy C₀ C x
    M.PosDef ∧ M ≤ 1 ∧ 1 ≤ M⁻¹ := by
  intro x M
  have hx : Fock.operatorMatrixPencilTopEdge C₀ C < x := by dsimp [x]; linarith
  obtain ⟨hp, hu⟩ := Fock.operatorMatrixPencilCauchy_posDef_and_le_inverse_edge_gap
    C₀ C hC₀ hC x hx
  have hl := Fock.operatorMatrixPencilCauchy_inverse_ge_edge_gap C₀ C hC₀ hC x hx
  have hgap : x - Fock.operatorMatrixPencilTopEdge C₀ C = 1 := by dsimp [x]; ring
  rw [hgap] at hu hl
  exact ⟨hp, by simpa using hu, by simpa using hl⟩

-- Positivity in a C-star state supplies the continuity needed for closure
-- freeness; no separate continuity premise is imposed on this use.
example {A I : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (φ : StarProbabilitySpace A) (B : I → Subalgebra ℂ A)
    (hf : FreelyIndependent φ.toProbabilitySpace B) :
    FreelyIndependent φ.toProbabilitySpace (fun i => (B i).topologicalClosure) :=
  hf.topologicalClosure φ.continuous_expectation

-- The actual inverses of two free variables satisfy centered factorization
-- on their explicit Neumann domains.
example {𝕜 A I : Type*} [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
    [CompleteSpace A] (φ : ProbabilitySpace 𝕜 A) (hφ : Continuous φ.expectation)
    (B : I → Subalgebra 𝕜 A) (hf : FreelyIndependent φ B)
    (i j : I) (hij : i ≠ j) (a b : A) (ha : a ∈ B i) (hb : b ∈ B j)
    (z w : 𝕜) (hz : ‖z • a‖ < 1) (hw : ‖w • b‖ < 1) :
    φ.expectation (φ.center (Ring.inverse (1 - z • a)) *
      φ.center (Ring.inverse (1 - w • b))) = 0 := by
  have h := hf.centered_inverse_ofFn_eq_zero hφ (n := 2) (by norm_num)
    ![i, j] (by
      intro k hk
      have hk0 : k = 0 := by omega
      subst k
      simpa using hij)
    ![a, b] (by intro k; fin_cases k <;> simp [ha, hb])
    ![z, w] (by intro k; fin_cases k <;> simp [hz, hw])
  simpa [List.ofFn_succ] using h

-- One-particle reflection gives a genuine full-Fock field reflection.
example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (h : H) :
    (Fock.secondQuantization (LinearIsometryEquiv.neg ℂ : H ≃ₗᵢ[ℂ] H)).conjStarAlgEquiv
      (Fock.tensorCreation H h + Fock.tensorAnnihilation H h) =
        Fock.tensorCreation H (-h) + Fock.tensorAnnihilation H (-h) := by
  simpa using Fock.secondQuantization_conj_field
    (LinearIsometryEquiv.neg ℂ : H ≃ₗᵢ[ℂ] H) h

-- Explicit actual inverse centering bound in the faithful closed Fock state.
example {I : Type*} (i : I) :
    ‖(Fock.closedGeneratedVacuumState I).toProbabilitySpace.center
      (Ring.inverse (1 - (1 / 8 : ℂ) • Fock.closedSemicircular i))‖ ≤ 2 / 3 := by
  letI : PartialOrder (Fock.closedSemicircularAlgebra I) := CStarAlgebra.spectralOrder _
  letI : StarOrderedRing (Fock.closedSemicircularAlgebra I) := CStarAlgebra.spectralOrderedRing _
  have hq : ‖(1 / 8 : ℂ) • Fock.closedSemicircular i‖ = (1 / 4 : ℝ) := by
    rw [norm_smul, Fock.norm_closedSemicircular]
    norm_num
  have h := (Fock.closedGeneratedVacuumState I).norm_center_inverse_one_sub_le
    ((1 / 8 : ℂ) • Fock.closedSemicircular i) (by rw [hq]; norm_num)
  rw [hq] at h
  norm_num at h
  exact h

-- Native matrix cones use the genuine bundled CP API for arbitrary Hilbert
-- embeddings, with no surjectivity or matrix-size restriction.
example {H K N : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] [Fintype N]
    (V : H →ₗᵢ[ℂ] K)
    (M : CStarMatrix N N (Fock.TensorFullFock K →L[ℂ] Fock.TensorFullFock K)) :
    0 ≤ (star M * M).map (Fock.secondQuantizationCompressionCP V) :=
  CompletelyPositiveMap.map_cstarMatrix_nonneg
    (Fock.secondQuantizationCompressionCP V) (star M * M) (star_mul_self_nonneg M)

noncomputable section
section ActualPositiveProductUsage
open scoped Topology
local instance (I : Type*) : PartialOrder (Fock.closedSemicircularAlgebra I) :=
  CStarAlgebra.spectralOrder _
local instance (I : Type*) : StarOrderedRing (Fock.closedSemicircularAlgebra I) :=
  CStarAlgebra.spectralOrderedRing _

-- Two positive free squared fields give an actual positive sandwich germ;
-- all three nonzero means are proved from the concrete state.
example {I : Type*} (i j : I) (hij : i ≠ j) :
    let φ := Fock.closedGeneratedVacuumState I
    let a := Fock.closedSemicircular i ^ 2
    let b := Fock.closedSemicircular j ^ 2
    ∃ hEa : φ.expectation a ≠ 0, ∃ hEb : φ.expectation b ≠ 0,
      ∃ hEP : φ.expectation (positiveMultiplicativeSandwich a b) ≠ 0,
        φ.sTransform (positiveMultiplicativeSandwich a b) hEP =ᶠ[𝓝 0]
          (fun w => φ.sTransform a hEa w * φ.sTransform b hEb w) := by
  intro φ a b
  have hf := Fock.freelyIndependent_closedGeneratedVacuumState I
  have ha : a ∈ Fock.closedGeneratorAlgebra i :=
    (Fock.closedGeneratorAlgebra i).pow_mem
      (Fock.closedSemicircular_mem_closedGeneratorAlgebra i) 2
  have hb : b ∈ Fock.closedGeneratorAlgebra j :=
    (Fock.closedGeneratorAlgebra j).pow_mem
      (Fock.closedSemicircular_mem_closedGeneratorAlgebra j) 2
  have hEa : φ.expectation a ≠ 0 := by simp [φ, a]
  have hEb : φ.expectation b ≠ 0 := by simp [φ, b]
  have hapos : @LE.le (Fock.closedSemicircularAlgebra I)
      (CStarAlgebra.spectralOrder (Fock.closedSemicircularAlgebra I)).toPreorder.toLE 0 a := by
    simpa only [(Fock.isSelfAdjoint_closedSemicircular i).star_eq, ← pow_two] using
      star_mul_self_nonneg (Fock.closedSemicircular i)
  have ht := Fock.closedGeneratedVacuumState_isTracial I
  refine ⟨hEa, hEb, φ.expectation_positiveMultiplicativeSandwich_ne_zero
    ht hf hij a b ha hb hapos hEa hEb, ?_⟩
  exact φ.sTransform_positiveMultiplicativeSandwich_eventually ht hf hij a b ha hb hapos hEa hEb
end ActualPositiveProductUsage
end

-- The entire join of the first two free algebras remains free from the third.
example {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
    (φ : ProbabilitySpace 𝕜 A) (B : Fin 3 → Subalgebra 𝕜 A)
    (hf : FreelyIndependent φ B) :
    FreelyIndependent φ ![B 0 ⊔ B 1, B 2] := by
  let g : Fin 3 → Fin 2 := ![0, 0, 1]
  apply (hf.groupedSubalgebra g).mono
  intro j
  fin_cases j
  · change B 0 ⊔ B 1 ≤ groupedSubalgebra B g 0
    exact sup_le (le_groupedSubalgebra B g (0 : Fin 3))
      (le_groupedSubalgebra B g (1 : Fin 3))
  · change B 2 ≤ groupedSubalgebra B g 1
    exact le_groupedSubalgebra B g (2 : Fin 3)

-- The actual doubled-algebra dilation fixes every included canonical Wick word at time zero.
example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (w : List (Fock.fullFockBasisSet H)) :
    Fock.ouTimeDilation H 0 (by norm_num)
      (Fock.tensorVectorWick ((w.map (Fock.fullFockBasis H)).map (Fock.doubledFirst H))) =
      Fock.tensorOperatorEquiv H (Fock.wick w) := by
  simpa using Fock.ouTimeDilation_canonicalWick (H := H) 0 (by norm_num) w

-- Faithfulness holds on the literal fixed tensor-model closure for an arbitrary ON family.
example {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : I → H) (he : Orthonormal ℂ e) (T : Fock.tensorFamilyAlgebra e)
    (hz : (Fock.tensorFamilyVacuumState e).expectation (star T * T) = 0) : T = 0 :=
  Fock.tensorFamilyVacuumState_faithful e he T hz

-- Two actual free half projections have the derived product mean 1/4.
example {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (φ : StarProbabilitySpace A) (hφ : IsTracial φ.toProbabilitySpace)
    {B : Fin 2 → Subalgebra ℂ A} (hf : FreelyIndependent φ.toProbabilitySpace B)
    (p : Fin 2 → A) (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) :
    φ.expectation (iteratedPositiveProduct 2 p) = (1 / 4 : ℂ) := by
  rw [φ.expectation_iteratedHalfProjectionProduct hφ 2 hf p hpB hp hE]
  norm_num

-- Time addition holds for every actual native-family algebra element, beyond Wick polynomials.
example {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : I → H) (he : Orthonormal ℂ e) (T : Fock.tensorFamilyAlgebra e) :
    Fock.familyOUTime e he 1 (by norm_num) (Fock.familyOUTime e he 2 (by norm_num) T) =
      Fock.familyOUTime e he 3 (by norm_num) T := by
  have h := Fock.familyOUTime_add e he 1 2 (by norm_num) (by norm_num) T
  have ht : (1 : ℝ) + 2 = 3 := by norm_num
  simp only [ht] at h
  exact h

-- A summable positive moment series at t=2 bounds the actual support by 1/2.
open MeasureTheory in
example (μ : Measure ℝ) (hpos : ∀ᵐ x ∂μ, 0 ≤ x)
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ)
    (hs : Summable (fun n : ℕ => (2 : ℝ) ^ n * ∫ x : ℝ, x ^ n ∂μ)) :
    μ.support ⊆ Set.Iic (1 / 2 : ℝ) :=
  support_subset_Iic_of_summable_positive_moments μ hpos hint 2 (by norm_num) hs

-- The complete cyclic L2 extension agrees with the actual algebra map on every vacuum vector.
example {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : I → H) (he : Orthonormal ℂ e) (t : ℝ) (ht : 0 ≤ t)
    (T : Fock.tensorFamilyAlgebra e) :
    Fock.familyOUL2 e he t ht (Fock.familyCyclicVector e T) =
      Fock.familyCyclicVector e (Fock.familyOUTime e he t ht T) :=
  Fock.familyOUL2_cyclicVector e he t ht T

-- An explicit scalar supersolution proves genuine infinite Picard-series convergence.
example : Summable (fun n : ℕ => halfProjectionPicardCoefficient 2 n * (1 / 2 : ℝ) ^ n) :=
  halfProjectionPicardCoefficient_summable 2 (1 / 2) (by norm_num) (1 / 2)
    (by norm_num) (by norm_num)

-- Strong time continuity recovers every native algebra element as time tends to zero.
open scoped Topology NNReal in
example {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : I → H) (he : Orthonormal ℂ e) (T : Fock.tensorFamilyAlgebra e) :
    Filter.Tendsto (fun t : ℝ≥0 => Fock.familyOUTime e he t t.coe_nonneg T)
      (𝓝 0) (𝓝 T) := by
  have h := (Fock.familyOUTime_strong_continuous e he T).continuousAt (x := (0 : ℝ≥0))
  simpa only [NNReal.coe_zero, Fock.familyOUTime_zero] using h.tendsto

-- Actual compression preserves arbitrary WOT limits; no uniform bound is needed for this fixed sandwich.
open scoped Topology in
example {X H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (V : H →ₗᵢ[ℂ] K) (l : Filter X)
    (T : X → (Fock.TensorFullFock K →WOT[ℂ] Fock.TensorFullFock K))
    (S : Fock.TensorFullFock K →WOT[ℂ] Fock.TensorFullFock K)
    (h : Filter.Tendsto T l (𝓝 S)) :
    Filter.Tendsto (fun x => Fock.secondQuantizationCompressionWOT V (T x)) l
      (𝓝 (Fock.secondQuantizationCompressionWOT V S)) :=
  ((Fock.secondQuantizationCompressionWOT_continuous V).tendsto S).comp h

-- The actual two-half-projection moment germ is the constructed analytic Picard fraction.
open scoped Topology in
example {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (φ : StarProbabilitySpace A) (hφ : IsTracial φ.toProbabilitySpace)
    {B : Fin 2 → Subalgebra ℂ A} (hf : FreelyIndependent φ.toProbabilitySpace B)
    (p : Fin 2 → A) (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) :
    φ.momentGeneratingFunction (iteratedPositiveProduct 2 p) =ᶠ[𝓝 0]
      (fun z => halfProjectionAnalyticSum 2 z / (1 - halfProjectionAnalyticSum 2 z)) :=
  φ.momentGeneratingFunction_eq_picard_fraction_eventually hφ 1 hf p hpB hp hE

-- Compression has trivial kernel on the entire included WOT closure of an arbitrary ON family.
example {I H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (V : H →ₗᵢ[ℂ] K) (e : I → H) (he : Orthonormal ℂ e)
    (T : Fock.tensorFamilyWOTAlgebra (fun i => V (e i)))
    (hz : Fock.includedFamilyWOTCompression V e T = 0) : T = 0 :=
  Fock.includedFamilyWOTCompression_eq_zero V e he T hz

-- The actual three-half-projection law has greatest support point 27/32.
example {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (φ : StarProbabilitySpace A) (hφ : IsTracial φ.toProbabilitySpace)
    {B : Fin 3 → Subalgebra ℂ A} (hf : FreelyIndependent φ.toProbabilitySpace B)
    (p : Fin 3 → A) (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) :
    IsGreatest (iteratedPositiveProbabilityLaw φ 3 p (fun i => (hp i).nonneg) : MeasureTheory.Measure ℝ).support
      (27 / 32 : ℝ) := by
  have h := φ.iteratedHalfProjection_law_support_isGreatest hφ 3 (by norm_num) hf p hpB hp hE
  have hedge : halfProjectionRightEdge 3 = (27 / 32 : ℝ) := by
    norm_num [halfProjectionRightEdge]
  rw [hedge] at h
  exact h

-- The length-two exterior branch has a unique positive parameter, without an upper bound on w.
example {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (φ : StarProbabilitySpace A) (hφ : IsTracial φ.toProbabilitySpace)
    {B : Fin 2 → Subalgebra ℂ A} (hf : FreelyIndependent φ.toProbabilitySpace B)
    (p : Fin 2 → A) (hpB : ∀ i, p i ∈ B i) (hp : ∀ i, IsStarProjection (p i))
    (hE : ∀ i, φ.expectation (p i) = (1 / 2 : ℂ)) (x : ℝ)
    (hx : halfProjectionRightEdge 2 < x) :
    ∃! w : ℝ, halfProjectionPhysicalDomain 2 w ∧ halfProjectionExteriorCurve 2 w = x :=
  φ.existsUnique_halfProjection_standard_physical_root hφ 2 (by norm_num) hf p hpB hp hE x hx

-- The full operator representation is recovered by actual Gamma compression, for arbitrary isometries.
example {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (V : H →ₗᵢ[ℂ] K) (T : Fock.TensorFullFock H →L[ℂ] Fock.TensorFullFock H) :
    Fock.secondQuantizationCompression V (Fock.isometryPrefixEmbedding V T) = T :=
  Fock.isometryPrefixEmbedding_compression V T

-- Literal generated double commutants transport for arbitrary field families.
example {I H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (V : H →ₗᵢ[ℂ] K) (e : I → H) (T : Fock.TensorFullFock H →L[ℂ] Fock.TensorFullFock H)
    (hT : T ∈ Set.centralizer (Set.centralizer (Set.range (Fock.tensorFamilyField e)))) :
    Fock.isometryPrefixEmbedding V T ∈ Set.centralizer
      (Set.centralizer (Set.range (Fock.tensorFamilyField (fun i => V (e i))))) :=
  Fock.isometryPrefixEmbedding_mem_familyDoubleCentralizer V e hT

-- Every integer-conjugated ENTIRE algebra copy is free, under the original entire-algebra freeness.
example {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    (φ : ProbabilitySpace ℂ A) (u : unitary A) (hu : IsHaarUnitary φ u)
    (B : Subalgebra ℂ A) (hf : FreelyIndependent φ (haarBasePair u B)) :
    FreelyIndependent φ (haarConjugatedAlgebra u B) :=
  freelyIndependent_haarConjugatedAlgebras φ u hu B hf

end FreeProbability.Examples
