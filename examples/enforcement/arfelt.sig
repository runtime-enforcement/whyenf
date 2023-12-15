ds_deletion_request(data:string, dataid:int, dsid:int)
ds_access_request(dsid:int)
ds_consent(dsid:int, data:string)
ds_restrict(data:string, dataid:int, dsid:int)
ds_repeal(data:string, dataid:int, dsid:int)
ds_object(dsid:int, data:string)
legal_grounds(dsid:int, data:string)
ds_revoke(dsid:int, data:string)
delete(data:string, dataid:int, dsid:int)+
grant_access(dsid:int)+
share_with(processorid:int, dataid:int)
inform(dsid:int)+
notify_proc(processorid:int, dataid:int)+
use(data:string, dataid:int, dsid:int)-
collect(data:string, dataid:int, dsid:int)
