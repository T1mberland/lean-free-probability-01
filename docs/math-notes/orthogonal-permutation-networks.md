# Actual finite permutation networks and genuine ordered cycle traces

Verified milestones on `feat/orthogonal-trace-words`:

- `7d80f0f`: `OrthogonalPermutationNetwork.lean`, actual power enumeration and
  independent orbit coloring/network factorization.
- `932ec1c`: `OrthogonalPermutationNetworkTrace.lean`, actual local and global
  ordered cycle-trace identities.

Both files are in `FreeProbability/RandomMatrix`. All earlier sources are
unchanged.

## Exact proved scope

For any finite index type `α`, actual permutation `σ`, and arbitrary complex
square matrices `M_a` with finite color index `n`, define the genuine network

```
Network(σ,M) = Σu:α→n ∏a M_a(u(a),u(σ(a))).
```

The orbit index is the actual quotient by `SameCycle σ`, including fixed
singleton orbits. Every quotient class has an actual finite orbit with
positive length. `permutationOrbitEnumeration` is an equivalence from
`Fin(length)` to that orbit whose value at `k` is literally `σ^k(c.out)`.
`permutationOrbitEnumeration_rotate` proves compatibility with genuine cyclic
successor, including the closing edge and length-one case. Neither a cyclic
enumeration nor a closing property is supplied as a premise.

The source proves the actual decomposition of sites into orbit fibers and
an equivalence between global colorings and independent orbit colorings.
Consequently `permutationNetwork_eq_prod_orbit_networks` factors the genuine
network into its actual orbit networks. The trace module then proves

```
Network(σ,M) = ∏c Tr(∏ordered k M_(enumeration(c,k))).
```

This is `permutationNetwork_eq_prod_cycle_traces`. Every ordered cycle product
uses the actual power enumeration just constructed. Singleton cycles
contribute their ordinary matrix trace. The source does not use a
nontrivial-cycle factorization that would discard them.

The local theorem `permutationOrbitNetwork_eq_trace` follows from the genuine
positive-length cyclic matrix identity `trace_ordered_product_eq_cyclic_sum`.
That identity is proved by actual matrix row expansion and an ordered product
of finite sums, reusing the already kernel-verified cyclic matrix-unit trace
calculation. It is not an additional trace formula assumption.

Explicit degenerate results:

- `permutationNetwork_empty_index`: empty `α` gives one, also when `n` is empty.
- `permutationNetwork_empty_dimension`: empty `n` and nonempty `α` give zero.
- `permutationNetwork_identity`: the identity permutation gives the product
  of EVERY singleton trace.

No trace, positivity, centering, matrix-norm or convergence hypotheses are
needed. Matrix color dimension can be empty. Positive cycle length is an
actual property of each orbit; a purported length-zero cyclic trace formula
would differ from the genuine trace of an empty matrix product and is not used.

## Verification and proof engineering

`7d80f0f` compiled without warnings (3027 jobs); all twelve public definitions
and theorems audited with only `propext`, `Classical.choice`, and `Quot.sound`.
`932ec1c` compiled without warnings (3030 jobs); all six public theorems have
the same standard dependencies. Source integrity, staged whitespace checks
and source review passed at both checkpoints; each source commit was pushed
immediately.

The enumeration uses the actual orbit's `IsCycleOn` theorem, bounded power
surjectivity, modular injectivity and closing at its genuine cardinality.
A rotation-value lemma with an independent natural length avoided dependent
rewrites in the actual cardinality index. Simplification rather than a raw
rewrite transported the equality-test condition with its decidable instance.
Kernel relations were made explicit when forming actual quotient witnesses.
Coloring inverse evaluation follows exact equivalence identities; function
composition and inverse-of-inverse normalization were explicitly exposed in
the local trace reindexing. None of these repairs changed a mathematical
statement or introduced a desired conclusion as a premise.

## Remaining original pairing-network obligations

This completes the generic permutation-network cycle-trace tool. The actual
paired row/column networks still require selecting one oriented half-orbit
in each raw two-involution component, exhausting each deterministic edge
once, and identifying its matrix or transpose label correctly. Only then
can these original pairing networks be transferred to this generic theorem.

Genuine Euclidean operator-norm bounds for the ordered cycle products and
traces are also separate and not asserted here. Their norm model must be
explicit (`Matrix.Norms.L2Operator` or literal `toEuclideanCLM` norm), rather
than default entrywise matrix norm. Combining contraction powers with sharp
Weingarten distances, centered leading-cycle cancellation, independent Haar
colors, fluctuations, concentration and random asymptotic freeness remain
later obligations.
