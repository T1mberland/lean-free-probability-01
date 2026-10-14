"""Conservative source guard; the Lean axiom audit is the authoritative axiom check."""
from pathlib import Path
import re

for path in [Path("FreeProbability.lean"), *Path("FreeProbability").rglob("*.lean")]:
    text = path.read_text()
    forbidden = re.search(r"\b(sorry|admit|axiom|unsafe|implemented_by|extern)\b", text)
    if forbidden:
        raise SystemExit(f"{path}: forbidden token {forbidden.group()}")
print("Proof-source integrity guard passed.")
