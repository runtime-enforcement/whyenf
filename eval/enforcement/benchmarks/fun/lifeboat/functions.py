owners = {}
consent = set()

def has_consent(dsid, data):
    return (dsid, data) in consent

def register_consent(dsid, data):
    consent.add((dsid, data))
    return 1

def revoke_consent(dsid, data):
    global consent
    if (dsid, data) in consent:
        consent.remove((dsid, data))
    return 1

def register_owner(data, dataid, dsid):
    owners[(data, dataid)] = dsid
    return 1

def owner(data, dataid):
    return owners.get((data, dataid), "None")