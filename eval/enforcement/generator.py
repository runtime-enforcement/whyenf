from random import choice, randint

SIG = {"ds_deletion_request": ["data", "dataid", "dsid"],
       "ds_access_request": ["dsid"],
       "ds_consent": ["dsid", "data"],
       "ds_restrict": ["data", "dataid", "dsid"],
       "ds_repeal": ["data", "dataid", "dsid"],
       "ds_object": ["dsid", "data"],
       "legal_grounds": ["dsid", "data"],
       "ds_revoke": ["dsid", "data"],
       "delete": ["data", "dataid", "dsid"],
       "grant_access": ["dsid"],
       "share_with": ["processorid", "dataid"],
       "inform": ["dsid"],
       "notify_proc": ["processorid", "dataid"],
       "use": ["data", "dataid", "dsid"],
       "collect": ["data", "dataid", "dsid"]}

GEN = {"data":   lambda _: f'"{randint(0, 3)}"',
       "dataid": lambda _: f'"{randint(0, 100)}"',
       "dsid":   lambda a: a["dataid"] if "dataid" in a else f'"{randint(0, 100)}"',
       "processorid": lambda _: f'"{randint(0, 5)}"'}

NAMES = list(SIG.keys())
    
""" Generates a random event """
def random_event():
    name = choice(NAMES)
    args = {}
    for arg_type in SIG[name]:
        args[arg_type] = GEN[arg_type](args)
    return name + "(" + ", ".join(args.values()) + ")"

""" Generates a random list of k events """
def random_tp(k):
    return " ".join([random_event() for _ in range(k)])

""" Generates a random trace with timestamps 1, ..., n and k events per time-point into fn """
def random_trace(n, k, fn):
    with open(fn, 'w') as f:
        for tp in range(n):
            f.write(f"{tp*1000}|@{tp} {random_tp(k)};\n")

if __name__ == '__main__':
    random_trace(1000, 5, 'synthetic.log')
                    
