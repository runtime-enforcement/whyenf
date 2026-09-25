#!/usr/bin/env python3
"""Check that PAPER.md only refers to existing Lean declarations, and that the
paper's claims (namespace `Enfflash.Paper`) use only the standard axioms.

Usage (from the `lean/` directory, after `lake build`):

    python3 scripts/check_paper_md.py

Every backticked identifier in the second column ("Lean") of the tables of
PAPER.md is checked with `#check`.
"""
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MD = ROOT / "PAPER.md"
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.₀-₉]*$")
STANDARD = {"propext", "Classical.choice", "Quot.sound"}

names = []
for line in MD.read_text().splitlines():
    if not line.startswith("|") or set(line) <= set("|-: "):
        continue
    cells = [c.strip() for c in line.strip().strip("|").split("|")]
    if len(cells) < 2 or cells[1] in ("Lean", ""):
        continue
    for tok in re.findall(r"`([^`]+)`", cells[1]):
        if IDENT.match(tok):
            names.append(tok)
names = sorted(set(names))

claims = re.findall(r"^theorem (\w+)", (ROOT / "Enfflash" / "Paper.lean").read_text(), re.M)

src = ["import Enfflash", "open Enfflash Enfflash.Examples", ""]
for n in names:
    src.append(f"#check @{n}")
for c in claims:
    src.append(f"#print axioms Enfflash.Paper.{c}")

with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
    f.write("\n".join(src) + "\n")
    tmp = f.name

out = subprocess.run(["lake", "env", "lean", tmp], cwd=ROOT, capture_output=True, text=True)
text = out.stdout + out.stderr

ok = True
errors = [l for l in text.splitlines() if "error" in l]
if errors:
    ok = False
    print("Unknown declarations in PAPER.md:")
    for l in errors:
        print("  " + l)

for m in re.finditer(r"'Enfflash\.Paper\.(\w+)' depends on axioms: \[([^\]]*)\]", text):
    axioms = {a.strip() for a in m.group(2).split(",") if a.strip()}
    extra = axioms - STANDARD
    if extra:
        ok = False
        print(f"Paper.{m.group(1)} uses non-standard axioms: {sorted(extra)}")
for m in re.finditer(r"'Enfflash\.Paper\.(\w+)' does not depend on any axioms", text):
    pass

print(f"checked {len(names)} declarations referenced by PAPER.md and "
      f"{len(claims)} claims in Paper.lean: {'OK' if ok else 'FAILED'}")
sys.exit(0 if ok else 1)
