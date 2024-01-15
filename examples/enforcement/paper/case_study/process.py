import pandas as pd
import numpy as np
import time

RAW = "raw.csv"
OUTPUT = "arfelt.log"

df = pd.read_csv(RAW, sep=";")
log = []

def ts(s):
    try:
        return time.mktime(time.strptime(s[:-4], '%Y-%m-%d %H:%M:%S')) // 86400
    except Exception:
        return np.nan

ts0 = ts(df.iloc[0]["Date"])

df["Date"] = df["Date"].apply(ts)
df = df[~df["Date"].isna()]
df = df.sort_values(by="Date")
df["Date"] -= ts0
df["Date"] = df["Date"].astype(int)

print(set(df["Title"]))

"""{
'Change phase to Complete', 
'Change phase to Abort', 
'Change Phase to End Report', 
'Change phase to Board meeting', 
'Change phase to Abandon', 
'Change phase to Review',
'Change phase to Preparation',
'Change Phase to Payout', 

'Reject', 
'Review',                                     *use*
'Account number changed', 
'Applicant justifies relevance',
'First payment', 
'Payment completed',                          *delete*
'Set to Pre-approved', 
'Fill out application',                       *ds_consent*
'Execute pre-decision', 
'Lawyer Review',                              *use*
'Inform applicant of approval',
'Register Decision',
'Screen application',                         *use*
'Architect Review',                           *use*
'Screening reject',
'Round ends',
'Round approved', 
'Approved - to board',
'Applicant informed',                         *delete*
'Execute abandon',                            *ds_deletion_request*
'Inform application of board review',
'Receive end report', 
'Approve'                                     *legal_grounds*
}"""

for _, row in df.iterrows():
    now = row["Date"]
    id = row["ID"]
    if row["Title"] == "Fill out application":
        line = f"@{now} ds_consent(\"{id}\", \"APPL\")"
    elif row["Title"] == "Payment completed":
        line = f"@{now} delete(\"APPL\",\"{id}\",\"{id}\") delete(\"ACCOUNT\",\"{id}\",\"{id}\")"
    elif row["Title"] == "Approve":
        line = f"@{now} legal_grounds(\"{id}\",\"ACCOUNT\")"
    elif row["Title"] == "Execute abandon":
        line = f"@{now} ds_deletion_request(\"APPL\",\"{id}\",\"{id}\")"
    elif row["Title"] == "Application informed":
        line = f"@{now} delete(\"APPL\",\"{id}\",\"{id}\")"
    elif row["Title"] in ["Review", "Lawyer Review", "Architect Review", "Screen application"]:
        line = f"@{now} use(\"APPL\",\"{id}\",\"{id}\")"
    else:
        pass
    log.append(line)

with open(OUTPUT, 'w') as f:
    for line in log:
        f.write(line + "\n")
