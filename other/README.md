# Structure

The overall structure of this artifact is presented below.

```
.
├── Dockerfile
├── monpoly
│   └── monpoly
├── whymon
│   └── bin
│       └── whymon.exe
└── whyenf
    ├── LICENSE
    ├── bin
    │   ├── whyenf.exe
    │   └── whyenf.ml
    ├── eval
    │   └── enforcement
    ├── examples
    │   └── case_study
    │       ├── formulae_enfpoly
    │       ├── formulae_whyenf
    │       └── formulae_whymon
    └── src
```

We omitted the details (files and folders) that are not relevant.
For instance, in our paper, we evaluated WhyEnf's performance and
compared it to EnfPoly's (MonPoly's enforcement mode) and WhyMon's,
but we will not include a description of EnfPoly's or WhyMon's
structure here.

# Content

## `monpoly/monpoly`

This file corresponds to EnfPoly's executable.

## `whymon/bin/whymon.exe`

This file corresponds to WhyMon's executable.

## `whyenf/bin/whyenf.ml`

This file contains the main OCaml module `Whyenf`.

## `whyenf/eval/enforcement`

This folder contains all scripts used to run WhyEnf's evaluation
as described in our paper.

## `whyenf/examples/case_study`

This folder contains all signatures, logs and formulae used in
WhyEnf's evaluation and in our running example (examples 1, 2,
3 and 5).

## `whyenf/src`

This folder contains WhyEnf's source code.

# Getting started

From within the extracted `whyenf-artifact` folder, run

```
$ docker build -t whyenf:artifact .
```

to build WhyEnf's image. Next, run

```
# docker run -it whyenf:artifact
```

to access the container.

# Smoke Test Instructions

Follow the instructions in this section to make sure that you
are able to execute WhyEnf, EnfPoly and all evaluation scripts.

## Lawfulness

To enforce the formula ϕ_law considering the trace σ_1 with WhyEnf, run

```
$ ./bin/whyenf.exe -sig examples/case_study/arfelt_et_al_2019.sig \
                   -formula examples/case_study/formulae_whyenf/lawfulness.mfotl \
                   -log examples/sigma1.log
```

from WhyEnf's root folder.
Here, the enforcer does not need to perform any actions (i.e.,
it does not cause nor supress any events).
Specifically, for the time-points specified in the trace, the
enforcer outputs `[Enforcer] @10 OK.` and `[Enforcer] @50 OK.`.
For all other time-points, the enforcer does not act
proactively, i.e., for all time-points `TP` between 11 and 49,
the output corresponds to `[Enforcer] @TP nothing to do proactively.`

To enforce the formula ϕ_law considering the trace σ_1 with EnfPoly, run

```
$ ../monpoly/monpoly -enforce \
                     -sig examples/case_study/arfelt_et_al_2019.sig \
                     -formula examples/case_study/formulae_enfpoly/lawfulness.mfotl \
                     -log examples/sigma1.log
```

from WhyEnf's root folder.


## Deletion

To enforce the formula ϕ_del considering the trace σ_2, run

```
$ ./bin/whyenf.exe -sig examples/case_study/arfelt_et_al_2019.sig \
                   -formula examples/case_study/formulae_whyenf/deletion.mfotl \
                   -log examples/sigma2.log
```

from WhyEnf's root folder.

# Replication instructions

This document describes how to reproduce the empirical evaluation presented in Section 6 and Appendix D of

Hublet, F., Lima, L., Basin, D., Krstić, S., & Traytel, D. (2024). Proactive Real Time First-Order Enforcement. *CAV'24*.

## Step 0. Requirements and preparation.

The configuration used for our experiments was as follows:

  * Processor: Intel i5-1135G7, 2.4 GHz
  * RAM: 32 GB
  * OS: Ubuntu 20.04.6

Descend to the evaluation folder with
```
cd ./whyenf/eval/enforcement
```

## Step 1 (optional). Preprocessing the log from Debois & Slaats (2015).

Indicative duration: < 1 minute.

You can run

```
python3 preprocess.py
```

to preprocess the raw log published by Debois & Slaats (2015) as specified by Arfelt et al. (2019) into the format used for our experiments.

The original csv file can be found at `examples/debois_slaats_2015.csv`.

If you set the constant `REPEATABLE` in `process.py` to `False`, this preprocesses the raw log for direct feeding into an enforcer. The preprocessed file is written to `examples/arfelt_et_al_2019.log`.

If you set the constant `REPEATABLE` in `process.py` to `True`, this preprocesses the raw log for usage by our repeater script (see below). The preprocessed file is written to `examples/arfelt_et_al_2019_repeatable.log`.

Note that we provide that the two preprocessed logs are already provided at the desired location in the repository.

## Step 2. Reproducing the type checking decisions for RQ1.

Indicative duration: < 1 minute.

You can type

```
../../bin/whyenf.exe -sig examples/arfelt_et_al_2019.sig -formula examples/formulae_whyenf/{formula}.mfotl -log examples/arfelt_et_al_2019.log
```

where `{formula}` is any of `minimization`, `limitation`, `lawfulness`, `consent`, `information`, `deletion`, or `sharing`, to see the type checking decisions and run the enforcer on the corresponding formula and log.

This experiment will use the following files:

  * The logs generated in the previous step;
  * The signature file in `examples/arfelt_et_al_2019.sig`;
  * The formulae in `examples/formulae_whyenf/`.

## Step 3. Reproducing the measurements with the log from Debois & Slaats (2015) for RQ2-3

Indicative duration: 1-3 hours.

You can run
```
python3 evaluate_rq2.py option [-e EXECUTABLE_PATH] [-g] [-s]
```
to run the performance measurements for RQ2-3 described in Section 7 and Appendix D and generate the corresponding graphs.

The options are as follows:

  * **Required**: `option` (possible values are `Enfpoly`, `WhyEnf`, and `WhyMon`) to select the tool to use as a backend;
  * `-e` to provide the path to the `Enfpoly` or `WhyMon` executable (required iff `OPTION = Enfpoly` or `WhyMon`);
  * `-g` to only regenerate the graphs and tables without performing new experiments;
  * `-s` to only run a smoke test without performing the full experiments.

This script uses the replayer script in `replayer.py`.

The experiments will use the following files:

  * The logs and signature file, as before;
  * The formulae in `examples/formulae_{tool}/`, where `{tool}` is one of `enfpoly`, `whyenf`, or `whymon`. The formulae in each of these folders adhere to the input grammar of the corresponding tool.

In `evaluate_rq2.py`,

After running the script, you will find:

  * Figure 8 (Sec. 7) at `out_whyenf/summary.png` (after running with `OPTION = WhyEnf`);
  * Figure 9 (Sec. 7) printed on standard input (after running with all three options);
  * Figure 13 (App. D) at `out_whymon/summary.png` (after running with `OPTION = WhyMon`);
  * Figure 14 (App. D) at `out_enfpoly/summary.png` (after running with `OPTION = Enfpoly`);
  * Figure 15 (App. D) at `out_whyenf/consent_400000.png`, `out_whyenf/information_1600000.png`, and `out_whyenf/sharing_1600000` (after running with `OPTION = WhyEnf`).

Note that for every experiment performed, the time profile is plotted to `out_{tool}/{formula}_{acceleration}.png`.

## Step 4. Reproducing the measurements with synthetic traces for RQ3.

Indicative duration: 1-3 hours.

You can run
```
python3 evaluate_rq3.py option [-e EXECUTABLE_PATH] [-g] [-s]
```
to run the performance measurements described in Section 7. The options are as in Step 3.

This script uses the replayer script in `replayer.py` and the trace generator in `generator.py`.

The experiments will use the following files:

  * A synthetic log that will be saved into `examples/synthetic.log`;
  * The signature file, as before;
  * The formulae in the `examples/formulae_{tool}/` folders.

After running the script, you will find:

  * Figure 10 (Sec. 7) printed on standard input (after running with all three options).

Note that for every experiment performed, the time profile is plotted to `out_{tool}/{formula}_{n}_{k}.png` where $n$ and $k$ are as in the paper.

# Testing

The correctness of WhyEnf has been tested through a combination of the following:

  * Comparison of WhyEnf's output to the output of Enfpoly (Hublet et al., 2022) on their common fragment.
  * Running of traces modified by WhyEnf through other monitors, especially WhyMon (Lima et al., 2024) and Monpoly (Basin et al., 2017).
  * Comparison of the output of WhyEnf to the findings reported in Arfelt et al. (2019).
  * Manual inspection on a set of elementary formulae and traces.

## References

Arfelt, Emma, David Basin, and Søren Debois (2019). "Monitoring the GDPR." *ESORICS'19*.

Basin, David A., Felix Klaedtke, and Eugen Zalinescu (2017). "The MonPoly Monitoring Tool." *RV-CuBES'17*.

Debois, Søren, and Tijs Slaats (2015). "The analysis of a real life declarative process." *SSCI'15*.

Hublet, François, David Basin, and Srđan Krstić (2022). "Real-time policy enforcement with metric first-order temporal logic." *ESORICS'22*.

Lima, Leonardo, Jonathan Julián Huerta y Munive, and Dmitriy Traytel (2024). "Explainable Online Monitoring of Metric First-Order Temporal Logic." *TACAS'24*.
