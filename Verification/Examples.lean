import FreeProbability

/-! Small applications of the public interfaces, checked with the audit target. -/

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

end FreeProbability.Examples
