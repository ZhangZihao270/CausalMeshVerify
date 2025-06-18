include "../DistributedSystem.i.dfy"
include "../../../Services/TPC/AppStateMachine.s.dfy"

module TpcRefinement__DistributedSystem_i {
import opened LiveTPC__DistributedSystem_i
import opened LiveTPC__Types_i
import opened Concrete_NodeIdentity_i
import opened AppStateMachine_s
import opened Collections__Seqs_s

datatype TPCSystemState = TPCSystemState(
    server_addresses : set<NodeIdentity>,
    // app : AppState,
    requests : set<Request>,
    replies : set<Reply>
)

predicate TpcSystemInit(s:TPCSystemState, server_addresses:set<NodeIdentity>)
{
    && s.server_addresses == server_addresses
    // && s.app == AppInitialize()
    && s.requests == {}
    && s.replies == {}
}

// function HandleRequest(s:AppState, req:AppRequest) : (AppState, int)
// {
//     var temp := AppHandleRequest(s, req);
//     if temp.1 == 0 then
//         (temp.0, 1)
//     else
//         (temp.0, 2)
// }

function HandleRequest(req:AppRequest) : int
{
    var vote := AppHandleRequest(req);
    if vote == 0 then
        1
    else
        2
}

predicate TpcSystemNextServerExecutesRequest(s:TPCSystemState, s':TPCSystemState, req:Request)
{
    // var temp := AppHandleRequest(s.app, req.req);
    // var decision := if temp.1 == 0 then Commit() else Abort();
    var vote := HandleRequest(req.req);
    var decision := if vote == 1 then Commit() else Abort();
    && s'.server_addresses == s.server_addresses
    && s'.requests == s.requests + {req}
    // && s'.app == temp.0
    && s'.replies == s.replies + {Reply(req.client, req.tid, decision)}
}

predicate TpcStateSequenceReflectsRequestExecution(s:TPCSystemState, s':TPCSystemState, req:Request)
{
    TpcSystemNextServerExecutesRequest(s, s', req)
}

predicate TpcStateSequenceReflectsRequestsExecution(s:TPCSystemState, s':TPCSystemState, intermediate_states:seq<TPCSystemState>, reqs:seq<Request>)
{
    && |intermediate_states| == |reqs| + 1
    && intermediate_states[0] == s 
    && last(intermediate_states) == s'
    && forall i :: 0 <= i < |reqs| ==> TpcSystemNextServerExecutesRequest(s, s', reqs[i])
}

// predicate TpcSystemNext(s:TPCSystemState, s':TPCSystemState)
// {
//     exists req:Request :: TpcSystemNextServerExecutesRequest(s, s', req)
// }

predicate TpcSystemNext(s:TPCSystemState, s':TPCSystemState)
{
    exists intermediate_states, reqs:seq<Request> :: TpcStateSequenceReflectsRequestsExecution(s, s', intermediate_states, reqs)
}

predicate TpcSystemRefinement(s:TpcState, ts:TPCSystemState)
{
    && (forall p :: p in s.environment.sentPackets && p.src in ts.server_addresses && p.msg.ReplyMsg?
        ==> Reply(p.dst, p.msg.tid, p.msg.reply) in ts.replies)
    && (forall req :: req in ts.requests ==> exists p :: p in s.environment.sentPackets && p.dst in ts.server_addresses && p.msg.RequestMsg?
                                        && req == Request(p.src, p.msg.tid, p.msg.req))
}

predicate TpcSystemBehaviorRefinementCorrect(server_addresses:set<NodeIdentity>, low_level_behavior:seq<TpcState>, high_level_behavior:seq<TPCSystemState>)
{
    && |high_level_behavior| == |low_level_behavior|
    && (forall i :: 0 <= i < |low_level_behavior| ==> TpcSystemRefinement(low_level_behavior[i], high_level_behavior[i]))
    && |high_level_behavior| > 0 
    && TpcSystemInit(high_level_behavior[0], server_addresses)
    && (forall i :: 0 <= i < |high_level_behavior| - 1 ==>
            TpcSystemNext(high_level_behavior[i], high_level_behavior[i+1]))
}
}