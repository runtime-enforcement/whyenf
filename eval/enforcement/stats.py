from pathlib import Path
import os
import subprocess
import pandas as pd
import re

def count_events(text):
    pattern = r'(\w+)\(((?:[^()"\']|"[^"]*"|\'[^\']*\')+)\)'
    matches = re.findall(pattern, text)
    return len(matches)

def parse_lifeboat_statistics(lifeboat_path : str, formula_folder : Path, formula_fn : str):
    lifeboat_path = lifeboat_path.format(str(formula_folder / formula_fn))
    result = subprocess.run(lifeboat_path, capture_output=True, text=True, shell=True)
    output = result.stdout

    size = re.search(r'Size of formula\s+(\d+)', output)
    size_unrolled = re.search(r'Size of formula \(unrolled\)\s+(\d+)', output)
    let_bindings = re.search(r'Let bindings\s+(\w+)', output)
    aggregations = re.search(r'Aggregations\s+(\w+)', output)
    function_applications = re.search(r'Function applications\s+(\w+)', output)

    data = {
        'name': formula_fn.replace(".mfotl", ""),
        'size': int(size.group(1)) if size else None,
        'unrolled_size': int(size_unrolled.group(1)) if size_unrolled else None,
        'has_let': let_bindings.group(1) if let_bindings else None,
        'has_agg': aggregations.group(1) if aggregations else None,
        'has_fun': function_applications.group(1) if function_applications else None
    }

    return pd.Series(data)


def print_log_statistics(
    option    : str, 
    benchmark : str,
    k         : int = 1,
) -> None:
    benchmark_path = Path('benchmarks') / benchmark / option
    logs_path      = benchmark_path / 'logs'

    log_fns = os.listdir(logs_path)
    log_rows = []
    for log_fn in log_fns:
        with open(logs_path / log_fn) as f:
            log_lines = f.readlines()
        name = log_fn.replace(".log", "")
        n_tp = len(log_lines) / k
        n_ts = (int(log_lines[-1].split("|")[0]) - int(log_lines[0].split("|")[0]) + 1) / k
        n_ev = sum(count_events(log_line) for log_line in log_lines) / k
        log_rows.append(pd.Series({"name": name, "n_tp": n_tp, "n_ts": n_ts, "n_ev": n_ev, "ev_r": n_ev / n_ts}))

    print(f"Log statistics for benchmark {benchmark} (option {option})")
    print(pd.DataFrame(log_rows).sort_values("n_ev"))
    print()

def print_formula_statistics(
    lifeboat_path : str,
    option        : str,
    benchmark     : str
) -> None:
    benchmark_path = Path('benchmarks') / benchmark / option
    formulae_path  = benchmark_path / 'formulae'

    formulae_fns = os.listdir(formulae_path)
    formulae_rows = []
    for formula_fn in formulae_fns:
        formulae_rows.append(parse_lifeboat_statistics(lifeboat_path, formulae_path, formula_fn))

    print(f"Formula statistics for benchmark {benchmark} (option {option})")
    print(pd.DataFrame(formulae_rows).sort_values("size"))
    print()

LIFEBOAT_PATH = "./lifeboat.exe -formula {} -statistics"
print_formula_statistics(LIFEBOAT_PATH, "lifeboat", "gdpr")
print_formula_statistics(LIFEBOAT_PATH, "lifeboat", "nokia")    
print_formula_statistics(LIFEBOAT_PATH, "lifeboat", "ic")
print_formula_statistics(LIFEBOAT_PATH, "lifeboat", "agg")
print_formula_statistics(LIFEBOAT_PATH, "lifeboat", "cluster")
print_formula_statistics(LIFEBOAT_PATH, "lifeboat", "fun")

print_log_statistics("lifeboat", "gdpr")
print_log_statistics("lifeboat", "nokia")
print_log_statistics("lifeboat", "ic")
print_log_statistics("lifeboat", "agg")
print_log_statistics("lifeboat", "cluster")
print_log_statistics("lifeboat", "fun")
