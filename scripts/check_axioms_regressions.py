"""Exercise the actual Lean audit against compiled positive/negative fixtures.

Run with `lake env python3 scripts/check_axioms_regressions.py`. Fixtures live
only in a temporary directory, never in the project library or source index.
"""

import os
from pathlib import Path
import subprocess
import tempfile

from check_axioms import ROOT, audit_source


def run_lean(path, root, env, output=None, extra_args=()):
    command = ["lean", f"--root={root}", *extra_args]
    if output is not None:
        command += ["-o", str(output)]
    return subprocess.run(command + [str(path)], cwd=ROOT, env=env,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)


def check_case(label, source, expected=None, module="FreeProbability.AuditProbe",
               dependency=None, compile_error=None):
    with tempfile.TemporaryDirectory(prefix="axiom-regression-") as directory:
        root = Path(directory)
        env = dict(os.environ)
        env["LEAN_PATH"] = str(root) + os.pathsep + env.get("LEAN_PATH", "")
        if dependency is not None:
            dep = root / "AuditDependency.lean"
            dep.write_text(dependency, encoding="utf-8")
            result = run_lean(dep, root, env, dep.with_suffix(".olean"))
            if result.returncode:
                raise SystemExit(f"{label}: dependency failed to compile\n{result.stdout}")
        modules = []
        if source is not None:
            fixture = root.joinpath(*module.split(".")).with_suffix(".lean")
            fixture.parent.mkdir(parents=True)
            fixture.write_text(source, encoding="utf-8")
            result = run_lean(fixture, root, env, fixture.with_suffix(".olean"),
                              ["--error=hasSorry"] if compile_error else [])
            if compile_error is not None:
                if result.returncode == 0 or compile_error not in result.stdout:
                    raise SystemExit(f"{label}: expected compilation failure\n{result.stdout}")
                print(f"PASS: {label}", flush=True)
                return
            if result.returncode:
                raise SystemExit(f"{label}: fixture failed to compile\n{result.stdout}")
            modules.append(module)
        audit = root / "Audit.lean"
        audit.write_text(audit_source(modules), encoding="utf-8")
        result = run_lean(audit, root, env)
        if expected is None:
            passed = result.returncode == 0 and "Axiom audit passed" in result.stdout
        else:
            passed = result.returncode != 0 and expected in result.stdout
        if not passed:
            raise SystemExit(f"{label}: unexpected audit result ({result.returncode})\n{result.stdout}")
        print(f"PASS: {label}", flush=True)


def main():
    check_case("ordinary proof and all three standard axioms", """
theorem good : True := True.intro
theorem ext (P Q : Prop) (h : P ↔ Q) : P = Q := propext h
noncomputable def choose {α : Sort u} (h : Nonempty α) : α := Classical.choice h
theorem sound {α : Sort u} {r : α → α → Prop} {a b : α} (h : r a b) :
    Quot.mk r a = Quot.mk r b := Quot.sound h
""")
    check_case("sorry", "theorem bad : False := by sorry\n", "Forbidden axiom sorryAx")
    check_case("admit", "theorem bad : False := by admit\n", "Forbidden axiom sorryAx")
    check_case("unused custom axiom", "axiom extra : False\n", "Forbidden axiom extra")
    check_case("unused private declaration", "private theorem hidden : False := by sorry\n",
               "Forbidden axiom sorryAx")
    check_case("modern module unused private declaration",
               "module\nprivate theorem hidden : False := by sorry\n", "Forbidden axiom sorryAx")
    check_case("other declaration namespace", "theorem Unrelated.bad : False := by sorry\n",
               "Forbidden axiom sorryAx")
    check_case("verification theorem", "theorem bad : False := by sorry\n",
               "Forbidden axiom sorryAx", module="Verification.AuditProbe")
    check_case("top-level verification axiom", "axiom extra : False\n",
               "Forbidden axiom extra", module="Verification")
    check_case("top-level verification private theorem", "private theorem hidden : False := by sorry\n",
               "Forbidden axiom sorryAx", module="Verification")
    check_case("transitive external axiom", "import AuditDependency\ntheorem bad : False := externalFact\n",
               "Forbidden axiom externalFact", dependency="axiom externalFact : False\n")
    check_case("native_decide compiler trust", "import Lean\ntheorem bad : 1 = 1 := by native_decide\n",
               "Forbidden axiom")
    check_case("anonymous example sorry is a build error", "example : True := by sorry\n",
               compile_error="declaration uses `sorry`")
    check_case("empty audit fails closed", None, "No project declarations were audited")


if __name__ == "__main__":
    main()
