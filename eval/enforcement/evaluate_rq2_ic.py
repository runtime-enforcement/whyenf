from typing import Dict, Any

from subprocess import Popen, PIPE, DEVNULL, STDOUT
from io import StringIO
import os.path

import argparse

from time import sleep, time
from math import log10

import pandas as pd
import matplotlib.pyplot as plt

from replayer import replay
from generator import random_trace

plt.rcParams["font.family"] = "serif"
plt.rcParams["font.serif"]  = "Times New Roman"
plt.rcParams["text.usetex"] = True

### Constants

FORMULAE_WHYENF_DIR = "examples_ic/formulae"

FORMULAE_WHYENF = {
    "Finalization_consistency": "finalization_consistency",
    "Finalized_height":         "finalized_height",
    "Replica_divergence":       "replica_divergence",
    "Block_validation_latency": "block_validation_latency",
    "Unauthorized_connections": "unauthorized_connections",
    "Reboot_count":             "reboot_count",  
    "Logging_behavior":         "logging_behavior__exe",
    "Clean_logs":               "clean_logs",
}

LOGS_WHYENF_DIR = "examples_ic/logs_repeatable"
LOGS_WHYENF = [
    "nightly_default_subnet_query_workload_long_duration_test__nightly_default_subnet_query_workload_long_duration_test-2982312912.log",
    "nightly_short_duration__xnet_slo_29_subnets_pot-2977769945.log",
    "nightly_short_duration__two_third_latency_pot-2982312911.log",
    "nightly_short_duration__xnet_slo_3_subnets_pot-2977769945.log",
    "hourly__create_subnet-2986511681.log",
    "hourly__tecdsa_signature_fails_without_cycles_pot-2987404546.log",
    "nightly_short_duration__network_reliability_pot-2977769945.log",
    "hourly__node_reassignment_pot-2987404546.log",
    "hourly__tecdsa_signature_from_nns_without_cycles_pot-2986511681.log",
    "hourly__unstuck_subnet_test_pot-2986511681.log",             
][::-1]

SIG = "examples_ic/predicates.sig"
LOG = "examples_ic/hourly__create_subnet-2986095401.log"

SUMMARY = "summary_ic.csv"
TABLE   = "table_ic.csv"
GRAPH   = "graph_ic.png"
  
PREFIX  = "> LATENCY "
SUFFIX  = " <"

### End constants

def summary(df : pd.DataFrame, a : float) -> Dict[str, Any]:
    return {"a": a,
            "n_ev": df["n_ev"].sum(),
            "n_tp": df["n_tp"].sum(),
            "cau": df["cau"].sum(),
            "sup": df["sup"].sum(),
            "ins": df["ins"].sum(),
            "avg_ev": df["n_ev"].sum() / (df["time"].max()-df["time"].min()) * 1000
                      if df["time"].max() != df["time"].min() else 0,
            "avg_latency": df["latency"].mean(),
            "avg_time": df["out_time"].diff().mean(),
            "max_time": df["out_time"].diff().max(),
            "max_latency": df["latency"].max()}

def table(df : pd.DataFrame) -> pd.DataFrame:
    series = []
    for formula, formula_df in df.groupby("formula"):
        avg_df = formula_df.groupby(["formula", "a", "d1"]).mean()
        ok_avg_df = avg_df[avg_df["max_latency"] <= avg_df.index.get_level_values("d1")].sort_index()
        best_avg_s = ok_avg_df.iloc[-1]
        series.append(pd.Series({"formula": formula,
                                 "a": ok_avg_df.index.get_level_values("a")[-1],
                                 "avg_latency": best_avg_s["avg_latency"],
                                 "max_latency": best_avg_s["max_latency"],
                                 "avg_time": best_avg_s["avg_time"],
                                 "max_time": best_avg_s["max_time"],
                                 "avg_ev": best_avg_s["avg_ev"]}))
    return pd.DataFrame(series)

def run_whymon(formula : str, log : str, a : float) -> pd.DataFrame:
    command = COMMAND.format(SIG, formula)
    print(command)
    log_path = LOGS_WHYENF_DIR + "/" + log
    with open(log_path, 'r') as f:
        max_tp = len(f.readlines()) - 1
    df = replay(log_path, max_tp, command, acc=a)
    series = []
    df = df.set_index(["type", "tp"])
    for (t, tp) in df.index:
        if t == 'f':
            try:
                the_f = df.loc[('f', tp)]
                the_r = df.loc[('r', tp)]
            except:
                continue
            series.append({'tp': tp,
                           'n_ev': the_r['n_ev'],
                           'n_tp': the_r['n_tp'],
                           'cau': the_r['cau'],
                           'sup': the_r['sup'],
                           'ins': the_r['ins'],
                           'time': the_f['ts'],
                           'latency': the_r['computer_time'] - the_f['computer_time'],
                           'out_time': the_r['computer_time']})
    return pd.DataFrame(series).sort_values(by="tp")

def plot(desc : str, a : float, df : pd.DataFrame, fn : str) -> None:
    fig, ax = plt.subplots(1, 1, figsize=(7.5, 2.5))
    real_time = 1000 / a
    df["time"] /= 1000
    ax.plot(df["time"], df["latency"], 'k-', label='latency (ms)', linewidth=0.5)
    ax.plot([min(df["time"]), max(df["time"])], [real_time, real_time], 'k:', label="real-time latency $1/a$ (ms)", linewidth=0.5)
    ax.plot([min(df["time"]), max(df["time"])], [max(df["latency"]), max(df["latency"])], 'k--', label="max latency $\mathsf{max}_{\ell}(a)$ (ms)", linewidth=0.5)
    df_ev = df[df["n_ev"] > 0]
    ax.plot(df_ev["time"], df_ev["n_ev"], 'b|', label='trace events', markersize=2)
    df_cau = df[df["cau"] > 0]
    ax.plot(df_cau["time"], df_cau["cau"], 'go', label='caused events', markersize=2)
    df_sup = df[df["sup"] > 0]
    ax.plot(df_sup["time"], df_sup["sup"], 'r^', label='suppressed events', markersize=2)
    ax.set_xlabel("time elapsed (s)")
    ax.set_title(f"“{desc}” policy, acceleration $a$ = {a:.0f} (1 second = {a:.0f} real-world seconds)")
    ax.legend(loc=('upper left'))
    fig.tight_layout()
    fig.savefig(fn, dpi=1000)
    plt.close()

if __name__ == '__main__':

    parser = argparse.ArgumentParser()
    parser.add_argument("option", help="Backend to test (WhyEnf)")
    parser.add_argument("-e", "--executable-path", help="Path to WhyEnf")
    parser.add_argument("-g", "--only-graph", action='store_true', help="Only generate the graph (do not run experiments)")
    parser.add_argument("-s", "--smoke-test", action='store_true', help="Only run smoke test (do not run experiments)")
    args = parser.parse_args()

    OPTION = args.option
    EXE = args.executable_path
    ONLY_GRAPH = args.only_graph
    SMOKE_TEST = args.smoke_test

    if OPTION == "WhyEnf":
        EXE      = EXE or '../../bin/whyenf.exe'
        COMMAND  = EXE + ' -sig {} -formula ' + FORMULAE_WHYENF_DIR + '/{}'
        FORMULAE = FORMULAE_WHYENF
        OUT      = "out_whyenf"
    
    series        = []
    STEP          = 100
    ACCELERATIONS = [5.12e7]
    N             = 1

    print(f"Running evaluation for RQ2-3 on logs from Basin et al. (2023), OPTION = {OPTION}, SMOKE_TEST = {SMOKE_TEST}")

    if not ONLY_GRAPH:
    
        for log in LOGS_WHYENF:

            for desc, formula in FORMULAE.items():
             
                for a in ACCELERATIONS:

                    for it in range(N):
                        print(f"OPTION = {OPTION}, formula = {desc}, log = {log}, a = {a}, it = {it+1}")
                        try:
                            df = run_whymon(formula + ".mfotl", log, a)
                        except Exception as e:
                            print(f"Failed with exception: {e}")
                            print("Skipping!")
                            continue
                        csv_fn = f"{formula}_{a}.csv"
                        png_fn = f"{formula}_{a}.png"
                        df.to_csv(os.path.join(OUT, csv_fn), index=False)
                        summ = summary(df, a)
                        summ["formula"] = desc
                        plot(desc, a, df, os.path.join(OUT, png_fn))
                        series.append(summ)
                        print(summ)
            
        summary_df = pd.DataFrame(series)
        summary_df.to_csv(os.path.join(OUT, SUMMARY), index=False)

    summary_df = pd.read_csv(os.path.join(OUT, SUMMARY))

    summary_df = summary_df[["formula", "a", "avg_ev", "avg_latency", "max_latency", "avg_time", "max_time"]]
    summary_df["d1"] = 1000 / summary_df["a"]

    print(table(summary_df).to_string())

    fig, ax2 = plt.subplots(1, 1, figsize=(7.5, 3))
    ax = ax2.twinx()
    
    d1 = summary_df[["a", "d1"]].groupby("a").mean()
    ax.plot(d1.index, d1["d1"], "k--", label="$1/a$", linewidth=1.5)
            
    for desc in FORMULAE_WHYENF:
        s = summary_df[summary_df["formula"] == desc][["a", "max_latency"]].groupby("a").mean()
        ax.plot(s.index, s["max_latency"], label=f'“{desc}”', linewidth=1.5)

    ae = summary_df[["a", "avg_ev"]].groupby("a").mean()
    ax2.plot(ae.index, ae["avg_ev"], "k:", label="avg. event rate", linewidth=0.5)

    ax2.set_xlabel("acceleration $a$")
    ax.set_ylabel("max latency $\mathsf{max}_{\ell}(a)$ (ms)")
    ax2.set_ylabel("events/s")

    if OPTION == "WhyEnf":
        ax.legend(loc='upper right')
        ax2.legend(loc='upper left')
        
    ax2.set_xscale('log')
    ax.set_yscale('log')     
    ax2.set_yscale('log')
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, GRAPH), dpi=300)

    plt.close()
        
    

