include "../../Common/Framework/AbstractService.s.dfy"
include "../../Common/Collections/Seqs.s.dfy"
include "AppStateMachine.s.dfy"

module AbstractServiceTPC_s refines AbstractService_s {
import opened Collections__Seqs_s
import opened AppStateMachine_s

datatype TpcRequest = TpcRequest(client:EndPoint, tid:int, request:AppRequest)
datatype TpcReply = TpcReply(client:EndPoint, tid:int, reply:AppReply)

datatype ServiceState' = ServiceState'(
    serverAddresses:set<EndPoint>,
    // app:AppState,
    requests:set<TpcRequest>,
    replies:set<TpcReply>
)

type ServiceState = ServiceState'

predicate Service_Init(s:ServiceState, serverAddresses:set<EndPoint>)
{
    && s.serverAddresses == serverAddresses
    // && s.app == AppInitialize()
    && s.requests == {}
    && s.replies == {}
}

predicate ServiceExecutesAppRequest(s:ServiceState, s':ServiceState, req:TpcRequest)
{
    var res := AppHandleRequest(req.request);
    var decision := if res == 0 then Commit() else Abort();
    && s'.serverAddresses == s.serverAddresses
    && s'.requests == s.requests + { req }
    // && s'.app == temp.0
    && s'.replies == s.replies + { TpcReply(req.client, req.tid, decision) }
}

predicate Service_Next(s:ServiceState, s':ServiceState)
{
    exists req :: ServiceExecutesAppRequest(s, s', req)
}

// predicate Service_Correspondence
}