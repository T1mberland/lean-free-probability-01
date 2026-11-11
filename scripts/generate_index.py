"""Generate a source-navigation index, not a Lean elaboration or proof certificate."""

import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "INDEX.json"
IDENT = r"(?:«[^»]+»|[\w'\u2080-\u209f]+)(?:\.(?:«[^»]+»|[\w'\u2080-\u209f]+))*"
DECL = re.compile(
    rf"^\s*(?P<prefix>(?:(?:@\[[^\]]*\]|private|protected|noncomputable|unsafe|partial)\s+)*)"
    rf"(?P<kind>theorem|lemma|def|abbrev|structure|inductive|class|opaque|axiom)\s+"
    rf"(?P<name>{IDENT})", re.MULTILINE
)
SCOPE = re.compile(rf"^\s*(?:noncomputable\s+)?(namespace|section|end)\b(?:[ \t]+({IDENT}))?", re.MULTILINE)


def mask_comments_and_strings(source):
    """Keep offsets/newlines while masking nested Lean comments and strings."""
    result = list(source)
    i, depth, string = 0, 0, False
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                result[i:i + 2] = "  "
                depth += 1
                i += 2
                continue
            if source.startswith("-/", i):
                result[i:i + 2] = "  "
                depth -= 1
                i += 2
                continue
        elif string:
            if source[i] == "\\":
                result[i] = " "
                i += 1
                if i < len(source) and source[i] != "\n":
                    result[i] = " "
                i += 1
                continue
            if source[i] == '"':
                string = False
        elif source[i] == "«":
            # Escaped identifiers may contain comment markers and quotes.
            end = source.find("»", i + 1)
            if end == -1:
                raise ValueError("Unclosed escaped identifier")
            i = end + 1
            continue
        elif source[i] == "'" and (char := re.match(r"'(?:\\[^\n]|[^'\\\n])'", source[i:])):
            # A quote character literal is not the start of a string.
            result[i:i + len(char[0])] = " " * len(char[0])
            i += len(char[0])
            continue
        elif source.startswith("/-", i):
            result[i:i + 2] = "  "
            depth = 1
            i += 2
            continue
        elif source.startswith("--", i):
            end = source.find("\n", i)
            end = len(source) if end == -1 else end
            result[i:end] = " " * (end - i)
            i = end
            continue
        elif source[i] == '"':
            string = True
        else:
            i += 1
            continue
        if source[i] != "\n":
            result[i] = " "
        i += 1
    if depth or string:
        raise ValueError("Unclosed comment or string")
    return "".join(result)


def declarations(source):
    text = mask_comments_and_strings(source)
    events = [(m.start(), "scope", m) for m in SCOPE.finditer(text)]
    events += [(m.start(), "declaration", m) for m in DECL.finditer(text)]
    scopes, found = [], []
    for _, kind, match in sorted(events):
        if kind == "scope":
            command, name = match.groups()
            if command == "end":
                if not scopes:
                    raise ValueError("Unmatched end command")
                _, opened = scopes.pop()
                if name and opened != name:
                    raise ValueError(f"Scope mismatch: end {name}, expected {opened}")
            else:
                scopes.append((command, name))
            continue
        namespace = ".".join(name for command, name in scopes if command == "namespace")
        found.append({
            "name": match.group("name"),
            "namespace": namespace,
            "kind": match.group("kind"),
            "line": source.count("\n", 0, match.start("kind")) + 1,
            "visibility": "private" if "private" in match.group("prefix").split() else "public",
        })
    return found


def build_index():
    paths = [ROOT / "FreeProbability.lean", *sorted((ROOT / "FreeProbability").rglob("*.lean"))]
    modules = []
    for path in paths:
        raw = path.read_bytes()
        source = raw.decode("utf-8")
        masked = mask_comments_and_strings(source)
        relative = path.relative_to(ROOT).as_posix()
        modules.append({
            "module": relative[:-5].replace("/", "."),
            "path": relative,
            "sha256": hashlib.sha256(raw).hexdigest(),
            "imports": re.findall(rf"^import[ \t]+({IDENT})", masked, re.MULTILINE),
            "declarations": declarations(source),
        })
    return {
        "schema_version": 1,
        "generator": "python3 scripts/generate_index.py",
        "scope": "FreeProbability.lean and FreeProbability/**/*.lean; dependencies and Verification excluded",
        "semantics": "Source-level navigation only. Names are written names plus lexical namespace, not elaborated Lean names. Private names are not public API. Types, assumptions, instances, structure fields, constructors and generated declarations are not indexed. Read the source and compile to establish a theorem's statement and validity.",
        "modules": modules,
    }


def render(index):
    # One declaration per line keeps diffs reviewable without excessive nesting.
    header = {key: value for key, value in index.items() if key != "modules"}
    lines = [json.dumps(header, ensure_ascii=False, indent=2)[:-2] + ',\n  "modules": [']
    for i, module in enumerate(index["modules"]):
        prefix = {key: value for key, value in module.items() if key != "declarations"}
        lines.append("    " + json.dumps(prefix, ensure_ascii=False)[:-1] + ', "declarations": [')
        lines.extend("      " + json.dumps(decl, ensure_ascii=False) + ("," if j + 1 < len(module["declarations"]) else "")
                     for j, decl in enumerate(module["declarations"]))
        lines.append("    ]}" + ("," if i + 1 < len(index["modules"]) else ""))
    return "\n".join([*lines, "  ]", "}", ""])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if INDEX.json is missing or stale")
    args = parser.parse_args()
    index = build_index()
    content = render(index)
    assert json.loads(content) == index
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text(encoding="utf-8") != content:
            raise SystemExit("INDEX.json is stale. Run python3 scripts/generate_index.py")
        print("Source index is current.")
    else:
        OUTPUT.write_text(content, encoding="utf-8")
        count = sum(len(module["declarations"]) for module in index["modules"])
        print(f"Indexed {count} named declarations in {len(index['modules'])} modules.")


if __name__ == "__main__":
    main()
