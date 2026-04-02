import os
import random
current_dir = os.path.dirname(os.path.abspath(__file__))

N_USERS = 10
LEN_TRACE = 1000000

def random_event():
    event_type = random.choice(["GiveConsent", "RevokeConsent", "Use"])
    user_id = random.randint(1, N_USERS)
    if event_type == "Use":
        resource_id = random.randint(1, 1000000)
        return f"{event_type}({user_id}, {resource_id});"
    else:
        return f"{event_type}({user_id});"

def generate_log(filename, n_events):
    with open(filename, "w") as f:
        for i in range(1, n_events + 1):
            event = random_event()
            f.write(f"@{i} {event}\n")

if __name__ == "__main__":
    log_file = os.path.join(current_dir, "consent.log")
    generate_log(log_file, LEN_TRACE)