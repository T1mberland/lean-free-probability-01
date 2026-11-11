# Free Probability in Lean 4

A Lean 4 library for noncommutative probability, free cumulants, Fock-space
models, spectral measures, matrix analysis and orthogonal Haar integration.

- [Theorem overview](THEOREMS.md): selected results and their hypotheses.
- [Source index](INDEX.json): generated module imports, declaration names and source locations.
- [Agent guide](AGENTS.md): navigation and change checks.

## Build and use

Install [elan](https://github.com/leanprover/elan) and Python 3, then run:

```sh
lake exe cache get
lake build
lake build Verification
python3 scripts/check_integrity.py
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/generate_index.py --check
lake env lean Verification/Axioms.lean
```

Use the committed toolchain and dependency manifest. The cache download is
optional; do not run `lake update` unless intentionally upgrading dependencies.
CI builds the library and verification modules and checks source integrity,
index freshness and transitive axioms.

```lean
import FreeProbability.Algebraic.ProbabilitySpace

open FreeProbability

example {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
    (φ : ProbabilitySpace 𝕜 A) (a : A) :
    φ.expectation (φ.center a) = 0 :=
  φ.expectation_center a
```

Import individual modules when possible; `import FreeProbability` imports the
whole library. Exact assumptions and mathematical conventions live in the Lean
statements. In particular, positivity and traciality are not implicit in
`ProbabilitySpace`, and moment convergence is not operator-norm convergence.

## Attribution and license

The library depends on [mathlib](https://github.com/leanprover-community/mathlib4).
Compact-Haar normalization proofs in
[OrthogonalHaar.lean](FreeProbability/RandomMatrix/OrthogonalHaar.lean) are adapted
from [lean-weingarten](https://github.com/T1mberland/lean-weingarten/tree/e3a09fdfaeeab526388990a52b9911dd8e955ab2),
with attribution in that file and the [Apache 2.0 text](LICENSES/Apache-2.0.txt)
retained. **No project-wide license has been specified.** The third-party license
does not license the entire repository.
