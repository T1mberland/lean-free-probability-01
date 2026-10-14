# CFC trace norm and the bounded-algebra L1 completion

This checkpoint constructs the actual absolute-value trace norm for an arbitrary
unital complex C-star algebra, a normalized positive state, and traciality.
Compatible `PartialOrder`/`StarOrderedRing` instances are the canonical C-star
order infrastructure. Faithfulness is needed only for injectivity and separation,
not for the norm equality or triangle inequality.

## Verified sources and publication

- `a19c63d`, `Analytic/TracialAbsoluteValue.lean`: actual
  `tracialAbsoluteValue T = CFC.sqrt (star T * T)`, positivity, square identity,
  operator norm equality, zero characterization, positive `tracialSize`,
  operator norm upper bound, and faithful separation of the size.
- `6211b70`, `Analytic/TracialDualNorm.lean`: actual continuous linear map
  `tracialDualEmbedding φ : A →L[ℂ] (A →L[ℂ] ℂ)`, evaluated as `φ(S*T)`.
  Operator norm contraction, faithful injection, trace symmetry, and dual triangle.
- `97b49d3`, `Analytic/TracialDualNormRegularization.lean`: actual real CFC
  `qε(a) = cfc (fun x => (x+ε)⁻¹) a`, positive for `a≥0`, `ε>0`, with
  `qε(a)(a+ε1)=1`, `qε(a)a²qε(a)≤1`, and `a−ε1≤qε(a)a²`.
- `6edb980`, `Analytic/TracialDualNormLower.lean`: actual bounded witness
  `Sε=qε(|T|)T*`, norm at most one, pairing at least `τ|T|−ε`, hence
  `tracialSize φ T ≤ ‖tracialDualEmbedding φ T‖`. This direction does not need
  traciality.
- `319a9c9`, `Analytic/TracialDualNormSquareRoot.lean`: actual real CFC factors
  `kε(a)=cfc sqrt(x+ε) a`, `gε(a)=cfc (sqrt(x+ε))⁻¹ a`, positive and satisfying
  `gεkε=1`, `kε²=a+ε1`, `gεa²gε≤a`.
- `ea36afb`, `Analytic/TracialDualNormUpper.lean`: genuine tracial
  Cauchy–Schwarz estimate, Hölder bound, exact
  `tracialDualEmbedding_norm_eq_size`, and `tracialSize_add_le`.
- `246a531`, `Analytic/TracialL1.lean`: actual complete normed complex space
  `tracialL1Space φ`, the norm closure of the trace-dual range. The bounded algebra
  has a dense continuous linear embedding, injective when faithful, with the
  exact trace norm when tracial. Every bounded test operator has a continuous
  pairing, and the expectation extends continuously.

All commits were immediately pushed to `origin/feat/tracial-l1-norm`.
All seven focused final module builds terminated with exit zero. The 36 direct
principal theorem audits (6+6+4+4+5+4+7, plus explicit CompleteSpace inference)
terminated with exit zero; dependencies are only `propext`, `Classical.choice`,
and `Quot.sound`. Source integrity and whitespace checks passed before each
source commit. Integration in main is a separate coordinator checkpoint.

## Upper bound and precise trace use

Set `a=|T|`, `X=Tgε(a)`, `Y=kε(a)S`. The genuine cone estimates give
`X*X≤a`, `YY*≤‖S‖²(a+ε1)`. Traciality gives
`τ(YX)=τ(gεkεST)=τ(ST)`. State Cauchy–Schwarz therefore yields
`|τ(ST)|²≤‖S‖²τ(a)(τ(a)+ε)`.
The limit is a division-safe elementary argument with
`ε=δ/(‖S‖²τ(a)+1)`. It covers `S=0` and `τ(a)=0`.
Combined with the explicit contraction witnesses this proves the dual norm
identity without polar decomposition, affiliated operators, or an assumed norm
axiom. The triangle inequality follows from the actual continuous dual norm.

## CFC implementation decisions

Reciprocal functions are continuous on the actual positive spectrum, not on all
of the real line. Spectrum positivity and `ε>0` discharge the only pole.
Use real CFC consistently for shifted reciprocals and square roots; the primitive
`CFC.sqrt` itself is NNReal CFC. Pointwise scalar inequalities are transferred by
`cfc_le_iff`; product identities use `cfc_mul` with explicit continuity arguments.
A broad rewrite of `a` by `cfc_id'` also rewrites the CFC base argument, so rewrite
only the intended side/occurrence. This was a genuine Lean elaboration issue,
resolved by typed intermediate identities rather than resource-limit changes.

## Remaining obligations

This is the genuine L1 completion of the bounded algebra in the proved trace
norm. It is not yet identified with affiliated measurable operators or a von
Neumann predual. Bounded bimodule multiplication, OU extension to L1,
noncommutative general Lp, relative entropy/data processing/lower semicontinuity,
and Goal 10 entropy estimates remain separate obligations. No entropy or full
Goal 10 completion is claimed by this checkpoint.
