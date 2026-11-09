# Contributing

## Reproducible setup

Install [elan](https://github.com/leanprover/elan) and Python 3. Use the committed
`lean-toolchain` and `lake-manifest.json`; do not run `lake update` for routine
builds. Toolchain or dependency upgrades should be separate, reviewed changes.

```sh
lake exe cache get
lake build
lake build Verification
python3 scripts/check_integrity.py
lake env lean Verification/Axioms.lean
```

The cache is optional; Lean still checks this project's sources. CI runs the
build, verification modules, source integrity guard and transitive axiom audit.
Do not describe a result as verified solely because a source guard passes.

## Mathematical review

- Keep changes focused and preserve existing public interfaces where possible.
- State domains and assumptions explicitly, especially positivity, traciality,
  faithfulness, normality and boundedness.
- Distinguish formal power series from analytic identities, moment convergence
  from norm convergence, and conditional interfaces from completed targets.
- Do not introduce `sorry`, `admit`, new mathematical axioms or kernel bypasses.
- Add useful usage examples and include new declarations in the verification
  coverage where appropriate. The axiom audit allows only `propext`,
  `Classical.choice` and `Quot.sound`.
- Check mathematical definitions and theorem statements as well as successful
  compilation. AI-generated code needs the same review as other contributions.
- Update the dependency audit and references when mathematical scope changes.

## Changes and attribution

Work on a topic branch and keep commits reviewable. Verify the exact proposed
revision before integration; preserve the stable branch and other contributors'
work. Do not commit local caches, temporary output or credentials.

Keep source attribution and third-party license notices. See
[docs/SOURCES.md](docs/SOURCES.md). A project-wide license has not yet been
specified; do not assume the included third-party license covers all files.
Historical execution records are not current contribution instructions.
