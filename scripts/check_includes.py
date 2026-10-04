#!/usr/bin/env python3
"""Verify that every code include in the prose is real and built.

For each {{#include path:anchor}} in docs/src this checks that the file
exists, that the anchor exists in it, and that the file is compiled by
`lake build` (a ZeroToQED module imported from the root module, or an
Examples module backing a lean_exe). Files under examples/smt/ are exempt
because they need lean-smt, which tracks its own Lean release.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DOCS = ROOT / "docs" / "src"
INCLUDE = re.compile(r"\{\{#include\s+([^}:\s]+)(?::([^}\s]+))?\s*\}\}")
UNBUILT = ("examples/smt/",)

root_imports = set(
    re.findall(r"^import\s+(\S+)", (ROOT / "src" / "ZeroToQED.lean").read_text(), re.M)
)
exe_roots = set(re.findall(r"root\s*:=\s*`(\S+)", (ROOT / "lakefile.lean").read_text()))

errors = []
seen = set()
for md in sorted(DOCS.glob("*.md")):
    for m in INCLUDE.finditer(md.read_text()):
        rel, anchor = m.group(1), m.group(2)
        target = (md.parent / rel).resolve()
        key = (target, anchor)
        where = f"{md.relative_to(ROOT)} -> {rel}" + (f":{anchor}" if anchor else "")
        if not target.exists():
            errors.append(f"missing file: {where}")
            continue
        if anchor and key not in seen:
            text = target.read_text()
            if not re.search(rf"ANCHOR:\s*{re.escape(anchor)}\b", text):
                errors.append(f"missing anchor: {where}")
            if not re.search(rf"ANCHOR_END:\s*{re.escape(anchor)}\b", text):
                errors.append(f"missing anchor end: {where}")
        seen.add(key)
        try:
            inside = target.relative_to(ROOT / "src")
        except ValueError:
            continue
        if inside.suffix != ".lean":
            continue
        module = ".".join(inside.with_suffix("").parts)
        if module.startswith("ZeroToQED.") and module not in root_imports:
            errors.append(f"not imported by src/ZeroToQED.lean: {module} ({md.name})")
        elif module.startswith("Examples.") and module not in exe_roots:
            errors.append(f"no lean_exe for: {module} ({md.name})")

unbuilt = sorted(
    str(t.relative_to(ROOT)) for t in {t for t, _ in seen} if str(t.relative_to(ROOT)).startswith(UNBUILT)
)
for e in sorted(set(errors)):
    print(e)
print(f"checked {len(seen)} includes; unbuilt (expected): {', '.join(unbuilt) or 'none'}")
sys.exit(1 if errors else 0)
