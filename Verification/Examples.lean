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

end FreeProbability.Examples
