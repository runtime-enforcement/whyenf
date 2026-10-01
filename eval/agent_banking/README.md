# Enforcing security policies on an LLM banking agent

This case study enforces ten MFOTL policies with EnfFlash on the tool calls of
an LLM agent, using the **banking suite of AgentDojo** (Debenedetti et al.,
NeurIPS 2024): 11 tools, 16 user tasks, 9 injection tasks, hence 16 benign and
144 attacked runs.

The agent is simulated by AgentDojo's **ground-truth tool calls**, so no LLM is
needed and every run is deterministic:

* a benign run executes the user task's calls;
* an attacked run executes them until the first tool output that contains the
  injection (the *hijack point*), then the injection task's calls (a fully
  hijacked agent), then the rest of the user task's calls.

Each call is sent to EnfFlash as one time-point *before* it executes; a
suppressed call is not executed (and a `Blocked` event is reported). Tool
outputs are turned into provenance events at the next time-point. Caused events
(`Notify`, `Audit`, `Escalate`) are recorded as the actions of fake tools.
AgentDojo's own checkers decide *utility* (the user task was done) and
*security* (the injection task was achieved) on the final environment.

## Signature (`policies/banking.sig`)

| Kind | Events |
|---|---|
| Session | `Session(s,u)`; `UserMentions(s,v)` for each token of the prompt (IBANs, words, amounts, quoted strings); `UserDoc(s,f)` for each file the prompt names |
| Writes (suppressable) | `SendMoney(c,s,u,r,a)`, `Schedule(c,s,u,r,a,rec)`, `Redirect(c,s,u,id,r)`, `Amend(c,s,u,id,a)`, `UpdatePassword(c,s,u,p)`, `UpdateUserInfo(c,s,u)`; `SubjTok(c,t)` for the tokens of a payment subject |
| Reads / outputs | `Read(c,s,u,tool)`; `Trusted(s,v)` (account data), `Untrusted(s,v)` (subjects of incoming transactions), `FromDoc(s,f,v)` and `DocAmount(s,f,a)` (contents of file `f`) |
| History | `Paid(u,r)`: payees of the account's past outgoing transactions |
| Feedback | `Blocked(s)`: the replayer reports a suppressed call |
| Causable | `Notify(u,k)`, `Audit(u,r,a)`, `Escalate(s)` |

Amounts are in cents; time is in minutes; every run has its own user and
session, so the per-user state of the first-order policies keeps runs apart.

## Policies (`policies/b*.mfotl`)

| | Policy | Needs |
|---|---|---|
| B1 | Pay or schedule only to a payee the user named, paid before, or found in a document the user named | first-order past |
| B2 | A payment subject may not contain account data read in the session unless the user supplied it | first-order past |
| B3 | At most €10,000 to one payee in 24 h | aggregation over a window |
| B4 | At most 3 outgoing transfers per user per hour | aggregation over a window |
| B5 | Redirect a standing order only to a payee the user named; always notify the owner | suppression + causation |
| B6 | Change the password only to one the user typed; always notify the owner | suppression + causation |
| B7 | Within 24 h of a profile or password change, pay only known payees | window, first-order |
| B8 | After a blocked write, block the session's writes for 1 h, and escalate once | window + causation |
| B9 | Log transfers above €1,000 and new recurring payments | causation |
| B10 | A payment to a payee known only from a document must use an amount stated in that document | first-order past |

`all.mfotl` is their conjunction (regenerate with `python3 make_all.py`).
`./check_policies.sh` compiles every policy and lists the events it causes (+)
and suppresses (-).

## Running

```sh
python3 -m venv .venv && .venv/bin/pip install agentdojo
./check_policies.sh
for p in none b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 all; do .venv/bin/python replay.py --policy $p; done
python3 report.py              # or: python3 report.py --latex
python3 matrix.py results/b1.json   # attack outcome per user task x injection task
.venv/bin/python replay.py --policy all --repeat 20 --out results/scaling   # long history
```

`ENFFLASH` selects the enforcer binary (default
`~/Git/whyenf/_build/default/bin/enfflash.exe`); `REPLAY_LOG=file` writes the
event log that was sent to it; `ENFFLASH_STDERR=file` keeps its stderr.
