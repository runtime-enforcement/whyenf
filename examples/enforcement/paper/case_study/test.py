from subprocess import Popen, PIPE, DEVNULL, STDOUT
from io import StringIO
import os.path

from time import sleep, time
from math import log10

import pandas as pd
import matplotlib.pyplot as plt

plt.rcParams["font.family"] = "serif"
plt.rcParams["font.serif"] = "Times New Roman"

WHYMON = ('docker run -i -v `pwd`:/work infsec/benchmark replayer -a {} -i monpoly -f monpoly arfelt.log -t {} | '
          '../../../../bin/whymon.exe -sig arfelt.sig '
          '-formula {}')

COLUMNS = ["time", "input_time_epoch", "ev", "tp", "cau", "sup", "ins", "output_time_epoch"]

TEMP = "temp.txt"

PREFIX = "> LATENCY "
SUFFIX = " <"

def analyze(lines, step):
    lines = [line[len(PREFIX):-len(SUFFIX)] for line in lines if line.startswith(PREFIX) and line.endswith(SUFFIX)]
    lines = [line.split(" ") for line in lines]
    df = pd.DataFrame(lines)
    df.columns = COLUMNS
    for column in COLUMNS:
        df[column] = df[column].astype(int)
    df["latency"] = df["output_time_epoch"] - df["input_time_epoch"]
    df["time"] *= step
    df.drop(columns=["input_time_epoch", "output_time_epoch"], inplace=True)
    df = df.iloc[:-1]
    return df

def summary(df, step, a):
    return {"a": a,
            "d1": 1000 * 24*3600 / a,
            "ev": df["ev"].sum(),
            "tp": df["tp"].sum(),
            "cau": df["cau"].sum(),
            "sup": df["sup"].sum(),
            "ins": df["ins"].sum(),
            "avg_ev": df["ev"].mean() * 1000 / step,
            "max_ev": df["ev"].max() * 1000 / step,
            "avg_latency": df["latency"].mean(),
            "max_latency": df["latency"].max(),
            "real_time_acc": 1000 * 24*3600 / df["latency"].max()}

def run_whymon(formula, step, a):
    command = WHYMON.format(a / (24*3600), step, formula)
    print(command)
    p = Popen([command], stdout=PIPE, stderr=PIPE, shell=True)
    output, err = p.communicate()
    p.wait()
    return analyze(output.decode('utf-8').split("\n"), step)

def plot(desc, step, a, df, fn):
    fig, ax = plt.subplots(1, 1, figsize=(7.5, 3))
    df["time"] /= 1000
    ax.plot(df["time"], df["latency"], 'k-', label='latency (ms)', linewidth=0.5)
    real_time = 1000 / (a / (24*3600))
    ax.plot([min(df["time"]), max(df["time"])], [real_time, real_time], 'k:', label="real-time latency (ms)", linewidth=0.5)
    ax.plot([min(df["time"]), max(df["time"])], [max(df["latency"]), max(df["latency"])], 'k--', label="max latency (ms)", linewidth=0.5)
    df_cau = df[df["cau"] > 0]
    ax.plot(df_cau["time"], df_cau["cau"], 'go', label='# caused events', markersize=2)
    df_sup = df[df["sup"] > 0]
    ax.plot(df_sup["time"], df_sup["sup"], 'r^', label='# suppressed events', markersize=2)
    #ax.set_ylabel('ms/event')
    ax.set_xlabel("time elapsed (s)")
    #ax.set_ylim([0, 17])
    ax2 = ax.twinx()
    ax2.plot(df["time"], df["ev"] * 1000 / step, 'b-', label='log(event rate)', linewidth=0.5)
    #ax2.set_ylabel('log(event/s)', color='b')
    ax2.set_yscale('log')
    ax2.tick_params(axis='y', labelcolor='b')
    ax.set_title(f"“{desc}” policy, acceleration = {a:.0f} (1 second = {a / (24*3600):.0f} days)")
    ax.legend(loc=(0.6, 0.47))
    ax2.legend(loc='upper left', labelcolor='b')
    fig.tight_layout()
    fig.savefig(fn, dpi=1000)

# number of caused and suppressed events


if __name__ == '__main__':
    FORMULAE = {
        "Access": "arfelt_6_access",
        "Erasure": "arfelt_7_erasure",
        "Lawfulness": "arfelt_3_lawfulness",
        "Limitation": "arfelt_2_limitation",
        "Information": "arfelt_5_information",
        "Share": "arfelt_7_erasure_3",
        "Consent": "arfelt_4_consent",
    }
    series = []
    STEP = 10
    OUT = "out"
    ACCELERATIONS = [0]#[0.25, 0.5e6, 0.75e6, 1e6]#1e3, 1e4, 1e5, 1e6]#[1.25e5, 2.5e5, 0.5e6, 1e6, 2e6, 4e6][::-1]
    N = 1
    for desc, formula in FORMULAE.items():

        for a in ACCELERATIONS:
            for _ in range(N):
                df = run_whymon(formula + ".mfotl", STEP, a)
                df.to_csv(os.path.join(OUT, f"{formula}_{a}.csv"), index=False)
                summ = summary(df, STEP, a)
                summ["formula"] = desc
                a = summ["real_time_acc"]
                plot(desc, STEP, a, df, os.path.join(OUT, f"{formula}_{a}.png"))
                series.append(summ)
                print(summ)
            
    summary = pd.DataFrame(series)
    summary.to_csv(os.path.join(OUT, "summary.csv"), index=None)

    summary = summary[["formula", "a", "d1", "avg_ev", "max_ev", "max_latency"]]

    fig, ax = plt.subplots(1, 1, figsize=(7.5, 3))
    
    d1 = summary[["a", "d1"]].groupby("a").mean()
    ax.plot(d1.index, d1["d1"], "k-", label="1/a", linewidth=0.5)
            
    for desc in FORMULAE:
        s = summary[summary["formula"] == desc][["a", "max_latency"]].groupby("a").mean()
        ax.plot(s.index, s["max_latency"], label=desc, linewidth=0.5)

    ax2 = ax.twinx()

    print(summary)
    
    me = summary[["a", "max_ev"]].groupby("a").mean()
    ax2.plot(me.index, me["max_ev"], "k--", label="max event rate", linewidth=0.5)

    ae = summary[["a", "avg_ev"]].groupby("a").mean()
    ax2.plot(ae.index, ae["avg_ev"], "k:", label="avg event rate", linewidth=0.5)

    ax.set_xlabel("acceleration a")
    ax.set_ylabel("max latency (ms)")
    ax2.set_ylabel("events/s")

    ax.legend(loc='upper left')
    ax2.legend(loc='upper right')
    ax.set_yscale('log')
    ax2.set_yscale('log')
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "graph.png"), dpi=1000)
        
    
