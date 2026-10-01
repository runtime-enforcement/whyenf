"""The EnfGuard benchmark suite of Table 1 (`tab:micro`): benchmarks, their
run parameters, and the tools compared (same values as evaluate_<benchmark>.py).
"""

from typing import Dict, List

# Benchmarks in table order, with their run parameters.
#   time_unit : seconds per log time unit
#   to        : timeout per run (s)
#   func      : pass the benchmark's functions.py (-func)
BENCHMARKS: Dict[str, dict] = {
    "gdpr":    {"time_unit": 24 * 3600, "to": 60,  "func": False},
    "fun":     {"time_unit": 24 * 3600, "to": 60,  "func": True},
    "cluster": {"time_unit": 1,         "to": 60,  "func": True},
    "agg":     {"time_unit": 1,         "to": 120, "func": False},
    "nokia":   {"time_unit": 1,         "to": 120, "func": False},
    "ic":      {"time_unit": 1,         "to": 600, "func": False},
}

N = 3  # repetitions per (formula, log)

# Enforcers (left part of the table) and monitors (right part, separated by ||).
ENFORCERS: List[str] = ["enfflash", "enfpoly", "enfguard", "dogwood"]
MONITORS: List[str] = ["monpoly"]

HEADERS: Dict[str, str] = {
    "enfflash": "Enfflash",
    "enfpoly":  "Enfpoly",
    "enfguard": "EnfGuard",
    "dogwood":  "Dogwood",
    "monpoly":  "Monpoly",
}

# Executable (symlink in eval/enforcement/) of each tool.
EXES: Dict[str, str] = {tool: f"./{tool}.exe" for tool in HEADERS}
