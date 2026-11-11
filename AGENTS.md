# Working with this library

- Start with `THEOREMS.md` for mathematical entry points, then search `INDEX.json`.
  Each module records its import name, path, SHA-256, direct imports and named
  source declarations. `line` is 1-based; `name` is the written name and
  `namespace` is its lexical namespace. Private entries are not reusable API.
- The index is a lexical navigation aid, not a Lean environment export or a
  verification report. It omits types, assumptions, instances, fields,
  constructors and generated declarations. Read the source statement and its
  surrounding variables; do not infer theorem scope from its name.
- Prefer narrow imports. Preserve existing public interfaces and dependency pins.
  Keep mathematical assumptions explicit. Do not add `sorry`, `admit`, new
  mathematical axioms or kernel bypasses. Review statements as well as proofs.
- Regenerate `INDEX.json` after source changes with
  `python3 scripts/generate_index.py`; never edit the index by hand. Update the
  short theorem overview when its entry points change.
- Run the checks in `README.md` before submitting changes. The source guard and
  index check alone do not establish compilation or mathematical correctness.
  The transitive axiom audit permits only `propext`, `Classical.choice` and
  `Quot.sound`. Add relevant usage examples under `Verification/`.
- Preserve attribution and license notices. Do not commit caches or credentials.
