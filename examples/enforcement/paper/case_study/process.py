import pandas as pd
import numpy as np
import time

RAW = "originallog.csv"
OUTPUT = "arfelt.log"

df = pd.read_csv(RAW, sep=";")
log = []

def date(s):
    try:
        return time.mktime(time.strptime(s[:-4], '%Y-%m-%d %H:%M:%S'))
    except Exception:
        return np.nan
    
def ts(s):
    try:
        return time.mktime(time.strptime(s[:-4], '%Y-%m-%d %H:%M:%S')) // 86400
    except Exception:
        return np.nan

df["Days"] = df["Date"].apply(ts)
df["Date"] = df["Date"].apply(date)
df = df[~df["Date"].isna()]
df = df.sort_values(by="Date")
df["Days"] = df["Days"].astype(int)

print(set(df["Title"]))

"""{nan,  ,  , , , , , , , , , , , , , , , ,, , 'Execute pre-decision', 'Round Ends', 'Undo payment', 'Første udbetaling', 'ansøger godtgør relevans af ansøgningen', 'Godkendelse - videre til bestyrelsen', 'Round approved', 'Godkend ansøgning', 'Register Decision'}"""

df.to_csv("intermediate.csv")

"""{
'Change phase to Complete',
'Change phase to Forberedelse',
'Change phase to Board meeting',
'Change Phase to Bortfaldet',
'Change phase to review',
'Change Phase to End Report',
'Change phase to Abort',
'Change Phase to Payout'

'Indledende afvisning',
'Udfoer bortfald',                            *ds_deletion_request*
'Review',                                     *use(APPL)*
'Pre-behandl ansøgning',                      *use(APPL)*
'Payment completed',                          *delete*
'Modtag slut rapport',
'Afvis ansøgning',
'Informer ansøger om at best ser på sagen',
'ansøger informeret ',                        *delete*
'Architect Review',                           *use*
'Fill out Application',
'Godkend ændret kontonummer',                 *use(ACCOUNT)*
'Lawyer Review',                              *use(APPL)*
'Informer ansøger om bevilling',
'Set to Pre-approved',
'Account number changed',                     *use(ACCOUNT)*
'Execute pre-decision',
'Round Ends', 
'Undo payment',                               *use(ACCOUNT)*
'Første udbetaling',                          *use(ACCOUNT)*
'ansøger godtgør relevans af ansøgningen',
'Godkendelse - videre til bestyrelsen',       *ds_consent*
'Round approved', 
'Godkend ansøgning',                          *legal_grounds*
'Register Decision',                       
}"""

for _, row in df.iterrows():
    now = row["Days"]
    id = row["ID"]
    if row["Title"] == "Godkendelse - videre til bestyrelsen":
        line = f"@{now} ds_consent(\"{id}\", \"APPL\")"
    elif row["Title"] == "Payment completed":
        line = f"@{now} delete(\"APPL\",\"{id}\",\"{id}\") delete(\"ACCOUNT\",\"{id}\",\"{id}\")"
    elif row["Title"] == "Godkend ansøgning":
        line = f"@{now} legal_grounds(\"{id}\",\"ACCOUNT\")"
    elif row["Title"] == "Udfoer bortfald":
        line = f"@{now} ds_deletion_request(\"APPL\",\"{id}\",\"{id}\")"
    elif row["Title"] == "ansøger informeret ":
        line = f"@{now} delete(\"APPL\",\"{id}\",\"{id}\")"
    elif row["Title"] in ["Review", "Lawyer Review", "Architect Review", "Pre-behandl ansøgning"]:
        line = f"@{now} use(\"APPL\",\"{id}\",\"{id}\")"
    elif row["Title"] in ["Godkent ændret kontonummer", "Account number changed", "Undo payment",
                          "Første udbetaling"]:
        line = f"@{now} use(\"ACCOUNT\",\"{id}\",\"{id}\")"
    else:
        continue
    log.append(line)

with open(OUTPUT, 'w') as f:
    for line in log:
        f.write(line + "\n")
