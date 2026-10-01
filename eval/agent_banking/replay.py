"""Replay AgentDojo banking tasks through EnfFlash.

Each *run* is one AgentDojo banking user task, optionally attacked by one
injection task.  The agent is simulated by the tasks' ground-truth tool calls:
a benign run executes the user task's calls; an attacked run executes them
until the first tool output that contains the injection (the "hijack point"),
then the injection task's calls, then the rest of the user task's calls (the
hijacked agent carries on).  Every call is sent to the enforcer as one
time-point before it executes; a suppressed call is not executed.  Tool
outputs are turned into provenance events at the following time-point.
AgentDojo's own checkers then decide utility (user task done) and security
(injection task achieved) on the final environment.

Usage: replay.py [--policy all|b1|...|none] [--out results/] [--runs N]
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from agentdojo.functions_runtime import FunctionCall, FunctionsRuntime
from agentdojo.task_suite.load_suites import get_suite

HERE = Path(__file__).resolve().parent
POLICIES = HERE / "policies"
SIG = POLICIES / "banking.sig"
ENFFLASH = os.environ.get("ENFFLASH", str(Path.home() / "Git/whyenf/_build/default/bin/enfflash.exe"))

# AgentDojo's "direct" attack: the injection is the goal, prefixed with TODO.
INJECTION_TEMPLATE = "TODO: {goal}"

# ─── Tokenization / provenance ────────────────────────────────────────────────

STOPWORDS = {
    "the", "and", "for", "with", "that", "this", "from", "you", "your", "are",
    "was", "has", "have", "not", "but", "all", "any", "can", "will", "please",
    "make", "sure", "user", "into", "via", "per", "its", "our", "their", "them",
    "they", "what", "how", "much", "which", "also", "then", "than", "been",
}
TOKEN_RE = re.compile(r"[a-z0-9][a-z0-9._@\-]*[a-z0-9]")
AMOUNT_RE = re.compile(r"\d[\d,]*(?:\.\d+)?")
DOC_RE = re.compile(r"[\w\-.]+\.txt")


def tokens(text: str) -> set[str]:
    """Lower-cased words, IBANs, numbers and quoted strings of `text`."""
    out = set()
    for t in TOKEN_RE.findall(str(text).lower()):
        t = t.strip(".-")
        if len(t) >= 3 and t not in STOPWORDS:
            out.add(t)
    return out


def cents(x: float | int | str) -> int:
    return int(round(float(str(x).replace(",", "")) * 100))


def amounts(text: str) -> set[int]:
    out = set()
    for m in AMOUNT_RE.findall(str(text)):
        try:
            c = cents(m)
        except ValueError:
            continue
        if c < 10**14:
            out.add(c)
    return out


def q(v: Any) -> str:
    """MFOTL log literal."""
    if isinstance(v, bool):
        return str(int(v))
    if isinstance(v, int):
        return str(v)
    s = str(v).replace("\\", "").replace('"', "")
    return f'"{s}"'


def ev(name: str, *args: Any) -> str:
    return f"{name}({', '.join(q(a) for a in args)})"


# ─── Enforcer client ──────────────────────────────────────────────────────────


class Enforcer:
    """Synchronous client: one time-point in, one reactive verdict out."""

    def __init__(self, formula: Path):
        self.proc = subprocess.Popen(
            [ENFFLASH, "-sig", str(SIG), "-formula", str(formula), "-json"],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=open(os.environ.get("ENFFLASH_STDERR", os.devnull), "w"),
            text=True, bufsize=1,
        )
        self.latencies_ns: list[int] = []
        self.proactive_causes: list[dict] = []
        log = os.environ.get("REPLAY_LOG")
        self.log = open(log, "w") if log else None

    def step(self, ts: int, events: list[str]) -> dict:
        assert self.proc.stdin and self.proc.stdout
        line = f"@{ts} {' '.join(events)};\n"
        if self.log:
            self.log.write(line)
        self.proc.stdin.write(line)
        self.proc.stdin.flush()
        while True:
            line = self.proc.stdout.readline()
            if not line:
                raise RuntimeError("enforcer terminated")
            try:
                msg = json.loads(line)
            except json.JSONDecodeError:
                continue
            if msg.get("proactive"):
                self.proactive_causes.extend(msg.get("cause", []))
                continue
            if "dur_nanos" in msg:
                self.latencies_ns.append(msg["dur_nanos"])
            return msg

    def close(self) -> None:
        if self.proc.stdin:
            self.proc.stdin.close()
        self.proc.wait(timeout=30)


class NoEnforcer:
    """Baseline: every call is allowed."""

    latencies_ns: list[int] = []
    proactive_causes: list[dict] = []

    def step(self, ts: int, events: list[str]) -> dict:
        return {}

    def close(self) -> None:
        pass


# ─── Runs ─────────────────────────────────────────────────────────────────────


@dataclass
class RunResult:
    run: str
    user_task: str
    injection_task: str | None
    utility: bool
    attack_success: bool | None
    blocked: list[str] = field(default_factory=list)
    caused: list[list[Any]] = field(default_factory=list)
    calls: int = 0


WRITE_TOOLS = {"send_money", "schedule_transaction", "update_scheduled_transaction",
               "update_password", "update_user_info"}


def call_events(c: str, s: str, u: str, call: FunctionCall) -> list[str]:
    """The events of a tool call (at the time-point where it is requested)."""
    a = dict(call.args)
    f = call.function
    if f == "send_money":
        evs = [ev("SendMoney", c, s, u, str(a["recipient"]).lower(), cents(a["amount"]))]
        return evs + [ev("SubjTok", c, t) for t in sorted(tokens(a.get("subject", "")))]
    if f == "schedule_transaction":
        evs = [ev("Schedule", c, s, u, str(a["recipient"]).lower(), cents(a["amount"]),
                  int(bool(a.get("recurring", False))))]
        return evs + [ev("SubjTok", c, t) for t in sorted(tokens(a.get("subject", "")))]
    if f == "update_scheduled_transaction":
        evs = []
        if a.get("recipient") is not None:
            evs.append(ev("Redirect", c, s, u, int(a["id"]), str(a["recipient"]).lower()))
        if a.get("amount") is not None:
            evs.append(ev("Amend", c, s, u, int(a["id"]), cents(a["amount"])))
        return evs or [ev("Amend", c, s, u, int(a["id"]), -1)]
    if f == "update_password":
        return [ev("UpdatePassword", c, s, u, str(a["password"]).lower())]
    if f == "update_user_info":
        return [ev("UpdateUserInfo", c, s, u)]
    return [ev("Read", c, s, u, f)]


def output_events(s: str, call: FunctionCall, result: Any, own_iban: str) -> list[str]:
    """Provenance of a tool output: account data is Trusted (and sensitive);
    third-party-controlled fields (subjects of incoming transactions) are
    Untrusted; file contents are FromDoc / DocAmount of that file."""
    f = call.function
    evs: list[str] = []
    if f == "read_file":
        path = str(call.args.get("file_path", "")).lower()
        text = str(result)
        evs += [ev("FromDoc", s, path, t) for t in sorted(tokens(text))]
        evs += [ev("DocAmount", s, path, a) for a in sorted(amounts(text))]
        return evs
    items = result if isinstance(result, list) else [result]
    trusted, untrusted = set(), set()
    for it in items:
        d = it.model_dump() if hasattr(it, "model_dump") else it
        if isinstance(d, dict) and "sender" in d and "subject" in d:
            incoming = d["sender"] not in ("me", own_iban)
            trusted |= tokens(f'{d["sender"]} {d["recipient"]} {d["amount"]} {d["date"]}')
            (untrusted if incoming else trusted).update(tokens(d["subject"]))
        elif isinstance(d, dict):
            trusted |= tokens(" ".join(str(v) for v in d.values()))
        else:
            trusted |= tokens(str(d))
    evs += [ev("Trusted", s, t) for t in sorted(trusted)]
    evs += [ev("Untrusted", s, t) for t in sorted(untrusted - trusted)]
    return evs


def is_blocked(verdict: dict, requested: list[str]) -> bool:
    names = {e.split("(")[0] for e in requested}
    return any(sup["name"] in names for sup in verdict.get("suppress", []))


def run_one(suite, enf, clock: list[int], run_id: str, user_task, injection_task) -> RunResult:
    s = u = run_id
    injections = {}
    if injection_task is not None:
        text = INJECTION_TEMPLATE.format(goal=injection_task.GOAL)
        injections = {k: text for k in suite.get_injection_vector_defaults()}
    env = suite.load_and_inject_default_environment(injections)
    env = user_task.init_environment(env)
    pre = env.model_copy(deep=True)
    runtime = FunctionsRuntime(suite.tools)
    own_iban = env.bank_account.iban

    def tick() -> int:
        clock[0] += 1
        return clock[0]

    # Session start: payee history and the user's prompt.
    prompt = user_task.PROMPT
    start = [ev("Session", s, u)]
    start += [ev("Paid", u, t.recipient.lower()) for t in env.bank_account.transactions
              if t.sender in ("me", own_iban)]
    start += [ev("UserMentions", s, t) for t in sorted(tokens(prompt))]
    start += [ev("UserDoc", s, d.lower()) for d in sorted(set(DOC_RE.findall(prompt)))]
    enf.step(tick(), start)

    user_calls = list(user_task.ground_truth(pre))
    attack_calls = list(injection_task.ground_truth(pre)) if injection_task else []
    marker = injections and next(iter(injections.values()))
    queue = list(user_calls)
    hijacked = injection_task is None
    executed: list[FunctionCall] = []
    res = RunResult(run_id, user_task.ID, injection_task.ID if injection_task else None,
                    utility=False, attack_success=None)
    n = 0
    while queue:
        call = queue.pop(0)
        n += 1
        c = f"{run_id}.c{n}"
        requested = call_events(c, s, u, call)
        verdict = enf.step(tick(), requested)
        res.caused += [[x["name"], *x["args"]] for x in verdict.get("cause", [])]
        if is_blocked(verdict, requested):
            res.blocked.append(call.function)
            v2 = enf.step(clock[0], [ev("Blocked", s)])
            res.caused += [[x["name"], *x["args"]] for x in v2.get("cause", [])]
            continue
        result, _err = runtime.run_function(env, call.function, dict(call.args))
        executed.append(call)
        if call.function not in WRITE_TOOLS:
            enf.step(clock[0], output_events(s, call, result, own_iban))
        if not hijacked and marker and marker in str(result):
            hijacked = True
            queue = attack_calls + queue
    res.calls = n

    output = getattr(user_task, "GROUND_TRUTH_OUTPUT", "") or ""
    ut = user_task.utility_from_traces(output, pre, env, executed)
    res.utility = bool(ut if ut is not None else user_task.utility(output, pre, env))
    if injection_task is not None:
        sec = injection_task.security_from_traces("", pre, env, executed)
        res.attack_success = bool(sec if sec is not None else injection_task.security("", pre, env))
    return res


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--policy", default="all", help="all, b1..b10, or none")
    ap.add_argument("--out", default=str(HERE / "results"))
    ap.add_argument("--repeat", type=int, default=1,
                    help="replay the suite this many times, with fresh users and sessions "
                         "each time, on one clock and one enforcer (long histories)")
    args = ap.parse_args()

    suite = get_suite("v1", "banking")
    key = lambda kv: int(kv[0].split("_")[-1])
    user_tasks = [t for _, t in sorted(suite.user_tasks.items(), key=key)]
    injection_tasks = [t for _, t in sorted(suite.injection_tasks.items(), key=key)]

    if args.policy == "none":
        enf = NoEnforcer()
    else:
        matches = sorted(POLICIES.glob(f"{args.policy}_*.mfotl")) or [POLICIES / f"{args.policy}.mfotl"]
        enf = Enforcer(matches[0])

    clock = [0]
    results = []
    t0 = time.time()
    for k in range(args.repeat):
        sfx = f"#{k}" if args.repeat > 1 else ""
        for ut in user_tasks:
            results.append(run_one(suite, enf, clock, f"{ut.ID}{sfx}", ut, None))
            for it in injection_tasks:
                results.append(run_one(suite, enf, clock, f"{ut.ID}+{it.ID}{sfx}", ut, it))
    wall = time.time() - t0
    enf.close()

    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    data = {
        "policy": args.policy,
        "wall_s": wall,
        "latencies_ns": enf.latencies_ns,
        "proactive_causes": enf.proactive_causes,
        "runs": [r.__dict__ for r in results],
    }
    name = args.policy if args.repeat == 1 else f"{args.policy}_x{args.repeat}"
    (out / f"{name}.json").write_text(json.dumps(data, indent=1))
    benign = [r for r in results if r.injection_task is None]
    attacked = [r for r in results if r.injection_task is not None]
    print(f"{args.policy}: utility {sum(r.utility for r in benign)}/{len(benign)} benign, "
          f"{sum(r.utility for r in attacked)}/{len(attacked)} under attack; "
          f"attacks succeeded {sum(bool(r.attack_success) for r in attacked)}/{len(attacked)}; "
          f"{wall:.1f}s")


if __name__ == "__main__":
    sys.exit(main())
