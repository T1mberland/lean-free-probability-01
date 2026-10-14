import FreeProbability.Analytic.ProjectionProductGrouped

/-! # Genuine finite iterated positive products and their generated-algebra membership -/

noncomputable section
namespace FreeProbability
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The actual iterated positive sandwich of a supplied finite tuple.
The empty product is the identity. -/
def iteratedPositiveProduct : (n : ℕ) → (Fin n → A) → A
  | 0, _ => 1
  | n + 1, p => positiveMultiplicativeSandwich
      (iteratedPositiveProduct n (fun i => p i.castSucc)) (p (Fin.last n))

/-- Every stage is genuinely positive when the supplied factors are positive. -/
theorem iteratedPositiveProduct_nonneg (n : ℕ) (p : Fin n → A)
    (hp : ∀ i, 0 ≤ p i) : 0 ≤ iteratedPositiveProduct n p := by
  cases n with
  | zero => exact zero_le_one
  | succ n => exact positiveMultiplicativeSandwich_nonneg _ _ (hp (Fin.last n))

/-- Every finite stage belongs to any actual closed star algebra containing
its supplied positive factors. Square-root membership is derived. -/
theorem iteratedPositiveProduct_mem_topologicalClosure (S : StarSubalgebra ℂ A)
    (n : ℕ) (p : Fin n → A) (hp : ∀ i, 0 ≤ p i)
    (hmem : ∀ i, p i ∈ S.topologicalClosure) :
    iteratedPositiveProduct n p ∈ S.topologicalClosure := by
  induction n with
  | zero => exact S.topologicalClosure.one_mem
  | succ n ih =>
    have hprefix := ih (fun i => p i.castSucc) (fun i => hp i.castSucc)
      (fun i => hmem i.castSucc)
    have hs := sqrt_mem_starSubalgebra_topologicalClosure S _ hprefix
      (iteratedPositiveProduct_nonneg n _ (fun i => hp i.castSucc))
    exact S.topologicalClosure.mul_mem (S.topologicalClosure.mul_mem hs (hmem (Fin.last n))) hs

/-- The actual finite product lies in the closed star algebra of precisely
its supplied factors. -/
theorem iteratedPositiveProduct_mem_generated (n : ℕ) (p : Fin n → A)
    (hp : ∀ i, 0 ≤ p i) :
    iteratedPositiveProduct n p ∈ closedStarGeneratedAlgebra (Set.range p) := by
  apply iteratedPositiveProduct_mem_topologicalClosure (StarAlgebra.adjoin ℂ (Set.range p))
    n p hp
  intro i
  exact mem_closedStarGeneratedAlgebra (Set.mem_range_self i)

/-- The last factor is separated from the genuine preceding finite tuple. -/
def prefixLastGroup (n : ℕ) (i : Fin (n + 1)) : Bool := decide (i.val = n)

@[simp] theorem prefixLastGroup_castSucc (n : ℕ) (i : Fin n) :
    prefixLastGroup n i.castSucc = false := by
  simp [prefixLastGroup, Nat.ne_of_lt i.isLt]

@[simp] theorem prefixLastGroup_last (n : ℕ) :
    prefixLastGroup n (Fin.last n) = true := by simp [prefixLastGroup]

/-- The preceding actual positive product belongs to the false group. -/
theorem iteratedPositiveProduct_mem_prefixGroup (n : ℕ) (p : Fin (n + 1) → A)
    (hp : ∀ i, 0 ≤ p i) :
    iteratedPositiveProduct n (fun i => p i.castSucc) ∈
      closedStarGeneratedAlgebra (groupedElementSet p (prefixLastGroup n) false) := by
  apply iteratedPositiveProduct_mem_topologicalClosure
    (StarAlgebra.adjoin ℂ (groupedElementSet p (prefixLastGroup n) false)) n
    (fun i => p i.castSucc) (fun i => hp i.castSucc)
  intro i
  exact mem_closedStarGeneratedAlgebra ⟨i.castSucc, prefixLastGroup_castSucc n i, rfl⟩

omit [PartialOrder A] [StarOrderedRing A] in
/-- The actual last factor belongs to the separate true group. -/
theorem last_mem_prefixGroup (n : ℕ) (p : Fin (n + 1) → A) :
    p (Fin.last n) ∈
      closedStarGeneratedAlgebra (groupedElementSet p (prefixLastGroup n) true) :=
  mem_closedStarGeneratedAlgebra ⟨Fin.last n, prefixLastGroup_last n, rfl⟩

end FreeProbability
