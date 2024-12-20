from subprocess import Popen, PIPE
import pandas as pd
from time import time, sleep
from multiprocessing import Process, Manager, Lock, Queue, TimeoutError
from io import StringIO
from tqdm import tqdm
import re

def read_log(log):
    df = pd.read_csv(log, header=None, names=["ts", "line"], sep="|")
    return df

def feeder(log, acc, p, q, queuing, lock):
    df = read_log(log)
    df["ts"] -= df["ts"].iloc[0]
    t0 = time()
    data = []
    for tp, row in df.iterrows():
        ts = int(row["ts"] / acc * 1000)
        while (time()-t0)*1000 < ts and queuing.value > 0:
            pass
        with lock:
            queuing.value += 1
        t = int(1000*time())
        p.stdin.write(row["line"] + "\n")
        p.stdin.write(f"> LATENCY {tp} {ts} <\n")
        p.stdin.flush()
        data.append(f"f,{tp},{ts},{t}")
    q.put(data)

PREFIX = "> LATENCY "
SUFFIX = " <"

def reader(p, q, queuing, lock, last_tp, desc):
    data = []
    tp = -1
    bar = tqdm(total=last_tp+1, desc=desc)
    while tp != last_tp:
        line = p.stdout.readline()
        if not line:
            break
        bar.update(n=tp+1-bar.n)
        if line.startswith(PREFIX):
            with lock:
                queuing.value -= 1
            rest = line[len(PREFIX):-len(SUFFIX)-1].split(" ")
            tp, ts = int(rest[0]), int(rest[1])
            others = ",".join(rest[2:])
            t = int(1000*time())
            data.append(f"r,{tp},{ts},{t},{others}")
    bar.update(n=1)
    q.put(data)

def replay(log, last_tp, command, desc, acc=1000, to=600):
    p = Popen(command, stdin=PIPE, stdout=PIPE, text=True, shell=True)
    manager = Manager()
    queuing = manager.Value('queuing', 0)
    q = Queue()
    lock = Lock()
    sleep(1)
    f = Process(target=feeder, args=(log, acc, p, q, queuing, lock))
    r = Process(target=reader, args=(p, q, queuing, lock, last_tp, desc))
    r.start()
    f.start()
    try:
        data1 = list(q.get(timeout=to))
        data2 = list(q.get(timeout=to))
    except:
        return None
    r.join()
    f.join()
    return pd.read_csv(StringIO("type,tp,ts,computer_time,n_ev,n_tp,cau,sup,ins,done_time\n" + "\n".join(data1 + data2)))

