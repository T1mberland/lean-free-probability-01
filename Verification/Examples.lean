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

end FreeProbability.Examples
