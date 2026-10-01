Session(s:string, u:string)
UserMentions(s:string, v:string)
UserDoc(s:string, f:string)
FromDoc(s:string, f:string, v:string)
DocAmount(s:string, f:string, a:int)
Trusted(s:string, v:string)
Untrusted(s:string, v:string)
Paid(u:string, r:string)
Read(c:string, s:string, u:string, tool:string)
SendMoney(c:string, s:string, u:string, r:string, a:int)-
Schedule(c:string, s:string, u:string, r:string, a:int, rec:int)-
SubjTok(c:string, t:string)
Redirect(c:string, s:string, u:string, i:int, r:string)-
Amend(c:string, s:string, u:string, i:int, a:int)-
UpdatePassword(c:string, s:string, u:string, p:string)-
UpdateUserInfo(c:string, s:string, u:string)-
Blocked(s:string)
Notify(u:string, k:string)+
Audit(u:string, r:string, a:int)+
Escalate(s:string)+
