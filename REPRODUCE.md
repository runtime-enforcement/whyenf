# Reproducing the paper's evaluation

Requirements: x86-64 Linux, Docker ≥ 23, git, ~12 GB of disk.

```sh
git clone --recurse-submodules <repository URL> enfflash && cd enfflash
eval/paper/docker/run.sh build     # build the image (~25 min)
eval/paper/docker/run.sh tables    # regenerate Tables 1-4 and the figures from the paper's results
```

Tables and figures are written to `eval/paper/output/{tables,figures}/`.

## Re-measuring

```sh
eval/paper/docker/run.sh table1.sh --tools all    # Table 1: EnfGuard suite
eval/paper/docker/run.sh table2.sh --tools all    # Table 2: GDPRSocial
eval/paper/docker/run.sh table3.sh --tools all    # Table 3: EventManager
eval/paper/docker/run.sh table4.sh --tools all    # Table 4: LLM banking agent
eval/paper/docker/run.sh rerun.sh  --tools all    # everything (about a day)
```

`--tools` also takes a subset of the tools a table measures (e.g. `--tools enfflash`).
Each script's other options are in its header. Measurements set the host's CPU
governor to `performance` with `sudo cpupower`; on a VM, prefix the command with
`GOVERNOR_CHECK=0`.

Without Docker: see [eval/paper/README.md](eval/paper/README.md).
