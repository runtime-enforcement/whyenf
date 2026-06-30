from pathlib import Path
from typing import Dict, List, Optional, Sequence
import pandas as pd # type: ignore
import json
import shutil
import subprocess
import tempfile
from time import time
from tqdm import tqdm # type: ignore

ENFGUARD_PATH  = Path("./_build/default/bin/enfflash.exe")
CONFIG  = Path("./tests/config.json")
SUMMARY = Path("./tests/summary.csv")
EXAMPLE = Path("./examples/tests")

class Test:

    command : List[str]

    def __init__(self, label : str, sig : Path, formula : Path, log : Path, output : str,
                 func : Optional[Path] = None, label_option : bool = False, success : bool = True,
                 state : Optional[Path] = None):
        self.label        = label
        self.sig          = sig
        self.formula      = formula
        self.log          = log
        self.output       = output
        self.func         = func
        self.label_option = label_option
        self.success      = success
        self.state        = state
        self._make_command()

    @classmethod
    def from_config(self, json_fn : Dict[str, str]) -> "Test":
        sig     = EXAMPLE / json_fn["sig"]
        formula = EXAMPLE / json_fn["formula"]
        log     = EXAMPLE / json_fn["log"]
        with open(EXAMPLE / json_fn["output"]) as f:
            output = f.read()
        func    = EXAMPLE / json_fn["func"] if "func" in json_fn else None
        success = (json_fn["success"] == True) if "success" in json_fn else True
        label_option = json_fn.get("label_option", False)
        state   = EXAMPLE / json_fn["state"] if "state" in json_fn else None
        return Test(json_fn["label"], sig, formula, log, output, func, label_option, success=success, state=state)

    def _make_command(self) -> None:
        command : List[str] = [str(ENFGUARD_PATH), "-sig", str(self.sig), "-formula", str(self.formula)]
        if self.func is not None:
            command += ["-func", str(self.func)]
        if self.log is not None:
            command += ["-log", str(self.log)]
        if self.label_option:
            command += ["-label"]
        if self.state is not None:
            command += ["-state", str(self.state)]
        self.command = command

    def _run_enfflash(self) -> subprocess.CompletedProcess[str]:
        # If a state file is involved, copy it to a temp file so the original is not mutated
        tmp_state = None
        command = list(self.command)
        if self.state is not None:
            tmp_state = tempfile.NamedTemporaryFile(suffix=".state", delete=False)
            shutil.copy2(str(self.state), tmp_state.name)
            # Replace the state path in the command
            idx = command.index("-state") + 1
            command[idx] = tmp_state.name
        try:
            result = subprocess.run(command, capture_output=True, text=True, timeout=5)
        except subprocess.TimeoutExpired:
            result = subprocess.CompletedProcess(args=command, returncode=-1, stdout="", stderr="Timeout occurred")
        finally:
            if tmp_state is not None:
                try:
                    Path(tmp_state.name).unlink(missing_ok=True)
                    Path(tmp_state.name + ".tmp").unlink(missing_ok=True)
                except Exception:
                    pass
        return result

    def run(self) -> pd.Series:
        print(f"Running test {self.label}...".ljust(48), end=' ')
        start_time = time()
        completed_process = self._run_enfflash()
        actual_success = completed_process.returncode == 0
        actual_output = completed_process.stdout
        end_time = time()
        delta_time = end_time - start_time
        if actual_output.strip() == self.output.strip() and actual_success == self.success:
            print(f"\033[1;32mPassed\033[0m ({delta_time:.3f}s)")
            return pd.Series({"label": self.label, "passed": True, "delta_time": delta_time,
                              "command": " ".join(self.command)})
        else:
            print(f"\033[1;31mError\033[0m  ({delta_time:.3f}s)")
            print(f"Expected success: {self.success}")
            print("Expected output:")
            print(self.output[:512])
            print(f"Actual success: {actual_success}")
            print("Actual output:")
            print(actual_output[:512])
            return pd.Series({"label": self.label, "passed": False, "delta_time": delta_time,
                              "command": " ".join(self.command)})

if __name__ == '__main__':

    with open(CONFIG, 'r') as f:
        configs = json.load(f)
    series = []
    for config in tqdm(configs):
        test = Test.from_config(config)
        series.append(test.run())
    df = pd.DataFrame(series)
    df.to_csv(SUMMARY, index=False)
    passed = df["passed"].sum()
    total  = df.shape[0]
    total_time = df["delta_time"].sum()
    if passed == total:
        print(f"\033[1;32mPassed all {total} tests!\033[0m ({total_time:.3f}s)")
    else:
        print(f"\033[1;31mPassed {passed} of {total} tests!\033[0m ({total_time:.3f}s)")
        print("Failed tests:")
        print(df[~df["passed"]].to_string())
