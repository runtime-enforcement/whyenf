from subprocess import Popen, PIPE
import pandas as pd
from time import time, sleep
from multiprocessing import Process, Manager, Lock, Queue
from io import StringIO

def feeder(log, acc, p, q, queuing, lock):
    df = pd.read_csv(log, header=None, names=["ts", "line"], sep="|")
    df["ts"] -= df["ts"].iloc[0]
    t0 = time()
    data = []
    for tp, row in df.iterrows():
        ts = int(row["ts"] / acc * 1000)
        while (time()-t0)*1000 < ts and queuing.value > 1:
            pass
        with lock:
            queuing.value += 1
        t = int(1000*time())
        p.stdin.write(row["line"] + "\n")
        p.stdin.write(f"> LATENCY {tp} {ts} <\n")
        p.stdin.flush()
        data.append(f"f,{tp},{ts},{t}")
    with lock:
        queuing.value = 0
    q.put(data)

PREFIX = "> LATENCY "
SUFFIX = " <"

def reader(p, q, queuing, lock):
    data = []
    while queuing.value > 0:
        line = p.stdout.readline()
        if not line:
            break
        print(line)
        if line.startswith(PREFIX):
            with lock:
                queuing.value -= 1
            rest = line[len(PREFIX):-len(SUFFIX)-1].split(" ")
            tp, ts = int(rest[0]), int(rest[1])
            others = ",".join(rest[2:])
            t = int(1000*time())
            data.append(f"r,{tp},{ts},{t},{others}")
    q.put(data)

def replay(log, command, acc=1000):
    p = Popen(command, stdin=PIPE, stdout=PIPE, text=True, shell=True)
    manager = Manager()
    queuing = manager.Value('queuing', 1)
    q = Queue()
    lock = Lock()
    sleep(1)
    f = Process(target=feeder, args=(log, acc, p, q, queuing, lock))
    r = Process(target=reader, args=(p, q, queuing, lock))
    f.start()
    r.start()
    data1 = list(q.get())
    data2 = list(q.get())
    return pd.read_csv(StringIO("type,tp,ts,computer_time,n_ev,n_tp,cau,sup,ins,done_time\n" + "\n".join(data1 + data2)))

    
print(replay("special.log", "../../../../bin/whymon.exe -mode light -sig arfelt.sig -formula rewritten/arfelt_6_access.mfotl", acc=1000))
