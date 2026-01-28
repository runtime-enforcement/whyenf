ds_deletion_request(data:string, dataid:string, dsid:string)
ds_access_request(dsid:string)
ds_consent(dsid:string, data:string)
ds_restrict(data:string, dataid:string, dsid:string)
ds_repeal(data:string, dataid:string, dsid:string)
ds_object(dsid:string, data:string)
legal_grounds(dsid:string, data:string)
ds_revoke(dsid:string, data:string)
delete(data:string, dataid:string, dsid:string)+
grant_access(dsid:string)+
share_with(processorid:string, dataid:string)
inform(dsid:string)+
notify_proc(processorid:string, dataid:string)+
use(data:string, dataid:string, dsid:string)-
collect(data:string, dataid:string, dsid:string)
