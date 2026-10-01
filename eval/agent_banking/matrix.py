"""Print the attack-success matrix (user task x injection task) of a result file."""
import json, sys
d = json.load(open(sys.argv[1]))
cell = {}
for r in d["runs"]:
    if r["injection_task"]:
        cell[(int(r["user_task"].split("_")[-1]), int(r["injection_task"].split("_")[-1]))] = r
print("ut\\inj " + " ".join(str(i) for i in range(9)))
for u in range(16):
    row = []
    for i in range(9):
        r = cell[(u, i)]
        row.append("X" if r["attack_success"] else ("b" if r["blocked"] else "."))
    print(f"{u:6d} " + " ".join(row))
print("X = attack succeeded, b = a call was blocked and the attack failed, . = failed without block")
