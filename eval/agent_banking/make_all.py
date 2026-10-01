"""Write policies/all.mfotl: the conjunction of the policies b1..b10."""
from pathlib import Path

POLICIES = Path(__file__).parent / "policies"
parts = sorted(POLICIES.glob("b*.mfotl"), key=lambda p: int(p.name[1:].split("_")[0]))
body = "\nAND\n".join(f"({p.read_text().strip()})" for p in parts)
(POLICIES / "all.mfotl").write_text(body + "\n")
print(f"all.mfotl: {len(parts)} policies")
