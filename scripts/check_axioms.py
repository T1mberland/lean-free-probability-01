"""Build and transitively audit every library and verification source module."""

from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
AUDIT = ROOT / "scripts" / "axiom_audit.lean"


def project_sources(root=ROOT):
    """Discover sources even when they are missing from the umbrella import."""
    sources = [root / "FreeProbability.lean"]
    for directory in ("FreeProbability", "Verification"):
        sources.extend(sorted((root / directory).rglob("*.lean")))
    return sources


def project_modules(root=ROOT):
    return [".".join(path.relative_to(root).with_suffix("").parts)
            for path in project_sources(root)]


def audit_source(modules):
    # `import all` also loads private declarations under Lean's module system.
    imports = "\n".join(f"import all {module}" for module in modules)
    return ("module\n" + imports + "\nmeta import Lean\nmeta import Lean.Util.CollectAxioms\n\n"
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
