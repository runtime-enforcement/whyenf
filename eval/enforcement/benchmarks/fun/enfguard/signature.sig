ds_deletion_request(data:string, dataid:string, dsid:string)
ds_consent(dsid:string, data:string)
legal_grounds(dsid:string, data:string)
ds_revoke(dsid:string, data:string)
delete(data:string, dataid:string, dsid:string)+
share_with(processorid:string, dataid:string)
inform(dsid:string)+
notify_proc(processorid:string, dataid:string)+
use(data:string, dataid:string, dsid:string)-
collect(data:string, dataid:string, dsid:string)

sfun has_consent(dsid:string, data:string): int
sfun register_consent(dsid:string, data:string): int
sfun revoke_consent(dsid:string, data:string): int
fun owner(data:string, dsid:string): string
sfun register_owner(data:string, dataid:string, dsid:string): int
call_function(fn:string, one:int)+