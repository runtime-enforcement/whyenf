from pathlib import Path
from typing import Optional, Sequence
import pandas as pd # type: ignore
import json
import subprocess
from time import time
from tqdm import tqdm # type: ignore

WHYENF  = Path("./_build/default/bin/whyenf.exe")
CONFIG  = Path("./tests/config.json")
SUMMARY = Path("./tests/summary.csv")
EXAMPLE = Path("./examples/tests")

class Test:

    command : list[str]

    def __init__(self, label : str, sig : Path, formula : Path, log : Path, output : str, 
                 func : Optional[Path] = None, success : bool = True):
        self.label   = label
        self.sig     = sig
        self.formula = formula
        self.log     = log
        self.output  = output
        self.func    = func
        self.success = success
        self._make_command()

    @classmethod
    def from_config(self, json_fn : dict[str, str]) -> "Test":
        sig     = EXAMPLE / json_fn["sig"]
        formula = EXAMPLE / json_fn["formula"]    
        log     = EXAMPLE / json_fn["log"]
        with open(EXAMPLE / json_fn["output"]) as f:
            output = f.read()
        func    = EXAMPLE / json_fn["func"] if "func" in json_fn else None
        success = (json_fn["success"] == True) if "success" in json_fn else True
        return Test(json_fn["label"], sig, formula, log, output, func, success=success)
    
    def _make_command(self) -> None:
        command : list[str] = [str(WHYENF), "-sig", str(self.sig), "-formula", str(self.formula), "-log", str(self.log)]
        if self.func:
            command += ["-func", str(self.func)]
        self.command = command
    
    def _run_whyenf(self) -> subprocess.CompletedProcess[str]:
        try:
            return subprocess.run(self.command, capture_output=True, text=True, timeout=1)
        except subprocess.TimeoutExpired:
            return subprocess.CompletedProcess(args=self.command, returncode=-1, stdout="", stderr="Timeout occurred")
    
    def run(self) -> pd.Series:
        print(f"Running test {self.label}...".ljust(48), end=' ')
        start_time = time()
        completed_process = self._run_whyenf()
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