"""Source guard; check_axioms.py is the authoritative transitive axiom check."""
import re

from check_axioms import project_sources
from generate_index import mask_comments_and_strings

FORBIDDEN = re.compile(
    r"\b(sorry|admit|axiom|unsafe|implemented_by|extern|sorryAx|native_decide|"
    r"ofReduceBool|ofReduceNat|debug\.skipKernelTC|debug\.proofAsSorry|warn\.sorry)\b"
)


def check_source(source):
    return FORBIDDEN.search(mask_comments_and_strings(source))


def main():
    for path in project_sources():
        forbidden = check_source(path.read_text(encoding="utf-8"))
        if forbidden:
            raise SystemExit(f"{path}: forbidden token {forbidden.group()}")
    print("Proof-source integrity guard passed (library and verification modules).")


if __name__ == "__main__":
    main()
