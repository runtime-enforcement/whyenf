# Regenerating the paper's evaluation tables

One script per experiment. Each reruns only the tools you pass with `--tools`
and then **always regenerates the full LaTeX table** from the stored results
of every tool (the latest run of each). Without `--tools`, it only regenerates
the table. Tables are written directly into the paper repository,
`~/Overleaf/Enfflash/tables/{tab_micro,tab_app1,tab_app2,tab_app3}.tex`, which `main.tex`
`\input`s (override the repository with `PAPER=`, or a file with `-o`).

| Script | Paper | Tools (`--tools`, or `all`) | Results used |
|---|---|---|---|
| `table1.sh` | Table 1, `tab:micro` (EnfGuard suite) | `enfflash,enfpoly,enfguard,dogwood,monpoly` | `eval/enforcement/outputs/<benchmark>/<tool>/summary.csv` |
| `table2.sh` | Table 2, `tab:app1` (GDPRSocial) | `enfflash,baseline` | `…/miniTwitter_gdpr/benchmark/privacy_testsuite/output/minitwitter_<policy>_<date>` |
| `table3.sh` | Table 3, `tab:app2` (EventManager) | `enfflash,dogwood,cedar` | `…/event_platform/benchmark/privacy_testsuite/output/event_platform_<policy>_<date>` |
| `table4.sh` | Table 4, `tab:app3` (LLM banking agent, AgentDojo) | `enfflash,enfguard,dogwood` | `eval/agent_banking/results/` |

To rerun **all** measurements of one or more tools, in every table that
measures them, use `rerun.sh` (it pins the governor once, then calls the
table scripts in order; logs in `eval/paper/logs/rerun_<date>/`):

    eval/paper/rerun.sh --tools dogwood                    # tables 1, 3, 4
    eval/paper/rerun.sh --tools enfflash,dogwood --tables 3,4
    eval/paper/rerun.sh --tools all --dry-run              # print the plan only

Examples:

    eval/paper/table1.sh --tools enfflash,dogwood        # all six benchmarks
    eval/paper/table1.sh --tools dogwood --benchmarks ic
    eval/paper/table2.sh --tools enfflash
    eval/paper/table3.sh --tools all
    eval/paper/table3.sh --tools enfflash,dogwood --cache off   # ablation without the result cache
    eval/paper/table3.sh                                       # table only
    eval/paper/table4.sh --tools all
    eval/paper/table4.sh --tools enfflash --repeat 50

Notes:

- **CPU governor.** Measurements only run with every CPU on the `performance`
  governor. The scripts switch to it with `sudo cpupower` (you may be asked for
  your password), restore the previous governor on exit, and refuse to run if
  this fails. The underlying runners (`evaluation.py`, `privacy_test.py`,
  `run_benchmark.sh`) refuse to run under any other governor as well.
- **Enfflash** is rebuilt (`dune build`) before it is measured, and the
  scripts use `_build/default/bin/enfflash.exe` (override with `ENFFLASH=`).
- **Table 1** puts the enforcers first (Enfflash, Enfpoly, EnfGuard, Dogwood)
  and Monpoly, a monitor, in a separate *Monitoring* column after `||`. The
  fastest *enforcer* of each row is in bold. Dogwood only has the 11 formulae
  it can express (`eval/enforcement/benchmarks/*/dogwood/`); the others show `--`.
  Benchmark parameters (time unit, timeout, repetitions) are in
  `eval/enforcement/suite.py`.
- **Table 2** runs Enfflash with `-fix-since` (the Lex-generated GDPRSocial
  policy has `S` operands with different free variables), passed through
  `INSTRLIB_EXTRA_ARGS`. The database/state snapshots are built once per
  invocation, with the enforced policy.
- **Table 3**: the three tools share the database snapshots, built once per
  invocation. `--cache off` turns off the result cache of both enforcers and
  selects the `…_nocache_…` runs for the table.
- **Table 4** replays AgentDojo's banking suite from its ground-truth tool
  calls (no LLM): 16 benign and 144 attacked runs, under no enforcement, each
  of the policies B1–B10 (`eval/agent_banking/policies/`) and their conjunction.
  *Prev.* counts the attacks that succeed without enforcement and fail with
  it, *FP* the benign runs with a blocked call, *Util.* the attacked runs
  whose user task still completes, *Caused* the Notify/Audit/Escalate events.
  *Online* is Enfflash's per-time-point latency during the replay; *Offline*
  is wall time per time-point of Enfflash (E) and EnfGuard (G) replaying the
  recorded event log (TO: timeout, `--timeout`, default 600 s). The last row
  replays the suite `--repeat` times (fresh users each time) through one
  enforcer. The enfflash run creates `eval/agent_banking/.venv` (AgentDojo) if
  missing. See `eval/agent_banking/README.md`.
- Other repositories: `PEL=` (proactive-enforcement-library, default
  `~/Git/proactive-enforcement-library`), `WHYENF=` (default `~/Git/whyenf`).
