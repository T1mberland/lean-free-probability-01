"""Build and transitively audit every library and verification source module."""

from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
AUDIT = ROOT / "scripts" / "axiom_audit.lean"


def project_sources(root=ROOT):
    """Discover sources even when they are missing from the umbrella import."""
    sources = []
    for library in ("FreeProbability", "Verification"):
        sources.append(root / f"{library}.lean")
        sources.extend(sorted((root / library).rglob("*.lean")))
    return sources


def project_modules(root=ROOT):
    return [".".join(path.relative_to(root).with_suffix("").parts)
            for path in project_sources(root)]


def audit_source(modules):
    # A legacy (non-`module`) consumer loads the private import level in Lean
    # 4.34, including private declarations of modern modules. It also accepts
    # this project's legacy modules, which a `module` consumer cannot import.
    imports = "\n".join(f"import {module}" for module in modules)
    return (imports + "\nimport Lean\nimport Lean.Util.CollectAxioms\n\n"
            + AUDIT.read_text(encoding="utf-8"))


def main():
    modules = project_modules()
    print(f"Building and auditing all {len(modules)} project modules.", flush=True)
    subprocess.run(["lake", "build", *modules], cwd=ROOT, check=True)
    (ROOT / ".lake").mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="axiom-audit-", dir=ROOT / ".lake") as directory:
        path = Path(directory) / "Audit.lean"
        path.write_text(audit_source(modules), encoding="utf-8")
        subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT, check=True)


if __name__ == "__main__":
    main()
