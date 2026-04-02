AcceptDataUsage(caller: string)
ActivityRecord(activity: string, property: string, value: string)+
Collect(activity: string, data: string, owner: string, purpose: string)
Consent(user: string, purpose: string)-
Contains(de: string, de2: string)+
ContainsData(de: string, f: string)+
ContestAccuracy(user: string, data: string, data': string)
DailyErasureReview(data: string)+
Declaration(de: string)+
Delete(d: string)+
HasCategory(d: string, cat: string)
HasIntendedRecipient(d: string, e: string)
HasText(de: string, text: string)+
Inform(c: string, ds: string, de: string)+
IsAdministrativeArrangement(ct: int, co: int, sg: int)
IsCompatibleWithPurpose(a: string, p: string)
IsConsentRequest(de: string)+
IsContractualClauses(ct: int, c: string, pr: string, c': string, pr': string, sg: int)
IsErasureRequest(rq: string, d: string)
IsFurtherCopy(rq: string)
IsHealthRelated(pi: string)
IsLastResortTransfer(re: string, c: string, c': string, pr': string, co: int, sg: int, i: string)+
IsNecessaryForImportantPublicInterest(a: string, pi: string)
IsNecessaryForJudicialClaims(a: string)
IsNecessaryForLegalObligation(a: string, l: string)
IsNecessaryForProtectionOfRights(a: string, e: string)
IsNecessaryForPublicInterest(a: string, pi: string)
IsNecessaryForSpecialMedicalReasons(a: string)
IsNecessaryForSubstantialPublicInterest(a: string)
IsNecessaryForVitalInterests(a: string, ds': string, v: string)
IsPortabilityRequest(rq: string)+
IsRecipientRequest(rq: string, d: string)
IsRestrictionRequest(rq: string, d: string, p: string)
IsSpecialData(d: string, sp: string)
IsStatutoryContractualRequirement(de: string, ds: string, d: string, r: string)+
IsStoragePeriod(de: string, t: int)+
LiftRestriction(c: string, d: string, rq: string)-
NotifyErasure(entity: string, data: string)+
NotifyRectification(entity: string, data: string, data': string)+
NotifyRestriction(entity: string, data: string, purpose: string)+
PersonalData(d: string, ds: string)
PersonalDataCopy(f: string, ds: string)+
Read(id: string, owner: string, activity: string, purpose: string, user: string)-
Rectify(d_old: string, d_new: string)+
RelatesToCriminalConvictionsOrOffences(d: string)
RequestAccess(user: string)
RequestObjection(user: string, purpose: string, de: string)
RequestRectification(user: string, data: string, data': string)
RequestResponse(ds: string, rq: string, rs: string)+
Revoke(user: string, purpose: string)-
Send(entity: string, data: string)
SendFile(entity: string, file: string)+
SpecialConsent(user: string, purpose: string, sp: string)-
SpecifiesNewController(rq: string, c': string)
TP(t: int)
Write(id: string, owner: string, activity: string, purpose: string, user: string)-
fun add_time_span(t: int, s: int) : int
fun string_of_category(cat: string) : string
fun string_of_country_io(co: int) : string
fun string_of_criteria(c: string) : string
fun string_of_data(d: string) : string
fun string_of_declaration(de: string) : string
fun string_of_ds(ds: string) : string
fun string_of_entity(c: string) : string
fun string_of_interest(i: string) : string
fun string_of_legal_basis(b: string) : string
fun string_of_purpose(p: string) : string
fun string_of_request(c: string) : string
fun string_of_safeguards(sg: int) : string
fun string_of_span(t: int) : string