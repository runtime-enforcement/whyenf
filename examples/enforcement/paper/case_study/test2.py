from subprocess import Popen, PIPE, DEVNULL, STDOUT
from io import StringIO
import os.path

from time import sleep, time
from math import log10

import pandas as pd
import matplotlib.pyplot as plt

from replayer import replay

plt.rcParams["font.family"] = "serif"
plt.rcParams["font.serif"] = "Times New Roman"
plt.rcParams["text.usetex"] = True

OPTION = "WhyEnf"

if OPTION == "Enfpoly":
    COMMAND = '~/Tools/monpoly_dev/monpoly/monpoly -enforce -sig arfelt.sig -formula formulae_enfpoly/{}  -ignore_parse_errors '
elif OPTION == "WhyEnf":
    COMMAND = '../../../../bin/whymon.exe -mode enforce -sig arfelt.sig -formula formulae_whyenf/{}'
elif OPTION == "WhyMon":
    COMMAND = '../../../../bin/whymon.exe -mode light -sig arfelt.sig -formula formulae_whymon/{}'
  

TEMP = "temp.txt"

PREFIX = "> LATENCY "
SUFFIX = " <"

def summary(df, step, a):
    return {"a": a,
            "n_ev": df["n_ev"].sum(),
            "n_tp": df["n_tp"].sum(),
            "cau": df["cau"].sum(),
            "sup": df["sup"].sum(),
            "ins": df["ins"].sum(),
            "avg_ev": df["n_ev"].sum() / (df["time"].max()-df["time"].min()) * 1000,
            "avg_latency": df["latency"].mean(),
            "max_latency": df["latency"].max()}

def run_whymon(formula, step, a):
    command = COMMAND.format(formula)
    print(command)
    df = replay("special.log", command, acc=a)
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
                           'latency': the_r['computer_time'] - the_f['computer_time']})
    return pd.DataFrame(series).sort_values(by="time")

def plot(desc, step, a, df, fn):
    fig, ax = plt.subplots(1, 1, figsize=(7.5, 3))
    real_time = (1000*24*3600) / a
    df["time"] /= 1000
    ax.plot(df["time"], df["latency"], 'k-', label='latency (ms)', linewidth=0.5)
    ax.plot([min(df["time"]), max(df["time"])], [real_time, real_time], 'k:', label="real-time latency $\delta_1(a)$ (ms)", linewidth=0.5)
    ax.plot([min(df["time"]), max(df["time"])], [max(df["latency"]), max(df["latency"])], 'k--', label="max latency $\ell(a)$ (ms)", linewidth=0.5)
    df_ev = df[df["n_ev"] > 0]
    ax.plot(df_ev["time"], df_ev["n_ev"], 'b|', label='trace events', markersize=2)
    df_cau = df[df["cau"] > 0]
    ax.plot(df_cau["time"], df_cau["cau"], 'go', label='caused events', markersize=2)
    df_sup = df[df["sup"] > 0]
    ax.plot(df_sup["time"], df_sup["sup"], 'r^', label='suppressed events', markersize=2)
    #ax.set_ylabel('ms/event')
    ax.set_xlabel("time elapsed (s)")
    #ax.set_ylim([0, 17])
    #ax2 = ax.twinx()
    #ax2.plot(df["time"], df["n_ev"] * 1000 / step, 'b-', label='log(event rate)', linewidth=0.5)
    #ax2.set_ylabel('log(event/s)', color='b')
    #ax2.set_yscale('log')
    #ax.set_yscale('log')
    #ax2.tick_params(axis='y', labelcolor='b')
    ax.set_title(f"“{desc}” policy, acceleration $a$ = {a:.0f} (1 second = {a / (24*3600):.0f} days)")
    ax.legend(loc=('upper left'))
    #ax2.legend(loc='upper left', labelcolor='b')
    fig.tight_layout()
    fig.savefig(fn, dpi=1000)

# number of caused and suppressed events


if __name__ == '__main__':
    if OPTION != "Enfpoly":
        FORMULAE = {
            "Consent": "arfelt_4_consent",
            "Information": "arfelt_5_information",
            "Share": "arfelt_7_erasure_3",
            "Lawfulness": "arfelt_3_lawfulness",
            "Limitation": "arfelt_2_limitation",
            "Erasure": "arfelt_7_erasure",
            "Access": "arfelt_6_access",
        }
    else:
        FORMULAE = {
            "Consent": "arfelt_4_consent",
            "Lawfulness": "arfelt_3_lawfulness",
        }
    series = []
    STEP = 100
    if OPTION == "Enfpoly":
        OUT = "out_monpoly"
    elif OPTION == "WhyEnf":
        OUT = "out_whyenf"
    elif OPTION == "WhyMon" :
        OUT = "out_whymon"
    ACCELERATIONS = [5e4, 1e5, 5e5, 1e6, 5e6, 1e7, 5e7]#[0.25, 0.5e6, 0.75e6, 1e6]#1e3, 1e4, 1e5, 1e6]#[1.25e5, 2.5e5, 0.5e6, 1e6, 2e6, 4e6][::-1]
    N = 1
    ONLY_GRAPH = True

    if not ONLY_GRAPH:
    
        for desc, formula in FORMULAE.items():

            for a in ACCELERATIONS:
                for _ in range(N):
                    df = run_whymon(formula + ".mfotl", STEP, a)
                    df.to_csv(os.path.join(OUT, f"{formula}_{a}.csv"), index=False)
                    summ = summary(df, STEP, a)
                    summ["formula"] = desc
                    #a = summ["real_time_acc"]
                    plot(desc, STEP, a, df, os.path.join(OUT, f"{formula}_{a}.png"))
                    series.append(summ)
                    print(summ)
            
        summary = pd.DataFrame(series)
        summary.to_csv(os.path.join(OUT, "summary.csv"), index=None)

    summary = pd.read_csv(os.path.join(OUT, "summary.csv"))

    summary = summary[["formula", "a", "avg_ev", "max_latency"]]
    summary["d1"] = (1000*24*3600) / summary["a"]

    fig, ax2 = plt.subplots(1, 1, figsize=(7.5, 3))
    ax = ax2.twinx()
    
    d1 = summary[["a", "d1"]].groupby("a").mean()
    ax.plot(d1.index, d1["d1"], "k--", label="$\delta_1(a)=1/a$", linewidth=1.5)
            
    for desc in FORMULAE:
        s = summary[summary["formula"] == desc][["a", "max_latency"]].groupby("a").mean()
        ax.plot(s.index, s["max_latency"], label=f'“{desc}”', linewidth=1.5)



    print(summary)
    
    ae = summary[["a", "avg_ev"]].groupby("a").mean()
    ax2.plot(ae.index, ae["avg_ev"], "k:", label="avg. event rate", linewidth=0.5)

    ax2.set_xlabel("acceleration $a$")
    ax.set_ylabel("max latency $\ell(a)$ (ms)")
    ax2.set_ylabel("events/s")

    ax.legend(loc='upper right')
    ax2.legend(loc='upper left')
    ax2.set_xscale('log')
    ax.set_yscale('log')    
    ax2.set_yscale('log')
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "graph.png"), dpi=300)
        
    
