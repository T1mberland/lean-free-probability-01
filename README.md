# Free Probability in Lean 4

[![Lean build + proof audit](https://github.com/T1mberland/lean-free-probability-01/actions/workflows/lean.yml/badge.svg?branch=cleanup%2Ffreeproblean-ready&event=push)](https://github.com/T1mberland/lean-free-probability-01/actions/workflows/lean.yml?query=branch%3Acleanup%2Ffreeproblean-ready)

A Lean 4 library for noncommutative probability, free cumulants, Fock-space
models, spectral measures, matrix analysis and orthogonal Haar integration.

- [Theorem overview](THEOREMS.md): selected results and their hypotheses.
- [Source index](INDEX.json): generated module imports, declaration names and source locations.

## Build and use

Install [elan](https://github.com/leanprover/elan) and Python 3, then run:

```sh
lake exe cache get
lake build
lake build Verification
lake exe mk_all --check
python3 scripts/check_integrity.py
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/generate_index.py --check
python3 scripts/check_axioms.py
lake env python3 scripts/check_axioms_regressions.py
LEAN_NUM_THREADS=1 lake env leanchecker -v FreeProbability Verification
```

Use the committed toolchain and dependency manifest. The cache download is
optional; do not run `lake update` unless intentionally upgrading dependencies.
CI builds the library and verification modules and checks source integrity,
index freshness, umbrella import coverage, transitive axioms and kernel replay.
The badge tracks this cleanup branch. Run `lake exe mk_all` after adding a module
to regenerate both umbrella files, then regenerate the source index. `mk_all`
returns a nonzero exit code when it updates files; rerun it with `--check`.

The source guard and axiom audit include both top-level files
`FreeProbability.lean` and `Verification.lean`, plus **every** module under their
directories, even if omitted from an umbrella import. The audit builds them and checks all
compiled declarations by their defining module, including private helpers,
generated declarations and declarations in other namespaces, and follows their
transitive dependencies. Only `propext`, `Classical.choice` and `Quot.sound`
(Lean's standard logical axioms used by mathlib) are allowed. `sorryAx`, added
mathematical axioms and compiler-trusting proofs such as `native_decide` fail
CI. This means **no `sorry` or extra axioms**, not "axiom-free mathematics."
Builds also promote Lean’s `hasSorry` diagnostic to an error, including in
anonymous `example` commands that are not retained as declarations. Regression
fixtures verify that forbidden cases really fail; comments and strings are
ignored by the separate source guard. `leanchecker` replays compiled declarations
from both libraries through Lean's kernel to detect environment manipulation.
It uses the same pinned Lean kernel, not an independent verifier, and does not
replace the axiom allowlist. CI uses one replay worker to limit memory usage
when loading mathlib. As with any CI, these checks
rely on the pinned Lean toolchain and trusted build/audit code.

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

## Source index

`INDEX.json` records each module's path, SHA-256, direct imports and named source
declarations (written name, lexical namespace, kind, visibility and 1-based line).
It is a navigation aid, not an elaborated Lean environment or verification
report. Types, assumptions, instances, fields, constructors and generated
declarations are omitted; private entries are not public API. Read the source
and compile before relying on a result.

Regenerate it after source changes with `python3 scripts/generate_index.py`.
Keep the short theorem overview current, preserve dependency pins and attribution,
and run the checks above. Review mathematical statements as well as proofs;
do not introduce `sorry`, new mathematical axioms or kernel bypasses.

## Attribution and license

This project is licensed under the [Apache License 2.0](LICENSE).

The library depends on [mathlib](https://github.com/leanprover-community/mathlib4).
Compact-Haar normalization proofs in
[OrthogonalHaar.lean](FreeProbability/RandomMatrix/OrthogonalHaar.lean) are adapted
from [lean-weingarten](https://github.com/T1mberland/lean-weingarten/tree/e3a09fdfaeeab526388990a52b9911dd8e955ab2),
with attribution in that file and the [Apache 2.0 text](LICENSES/Apache-2.0.txt)
retained. Third-party dependencies retain their respective licenses.
