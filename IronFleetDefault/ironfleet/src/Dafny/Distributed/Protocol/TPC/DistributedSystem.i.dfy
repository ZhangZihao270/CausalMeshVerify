include "Constants.i.dfy"
include "Message.i.dfy"
include "Host.i.dfy"
include "../Common/NodeIdentity.i.dfy"

module LiveTPC__DistributedSystem_i {
import opened LiveTPC__Constants_i
import opened LiveTPC__Configuration_i
import opened LiveTPC__Message_i
import opened LiveTPC__Host_i
import opened Environment_s
import opened Concrete_NodeIdentity_i

datatype TpcState = TpcState(
    constants : Constants,
    environment : LEnvironment<NodeIdentity, TpcMessage>,
    hosts : seq<LScheduler>,
    clients : set<NodeIdentity>
)

predicate TpcMapsComplete(s:TpcState)
{
    |s.hosts| == |s.constants.config.node_ids|
}

predicate TpcConstantsUnchanged(s:TpcState, s':TpcState)
{
    && |s'.hosts| == |s.hosts|
    && s'.clients == s.clients
    && s'.constants == s.constants
}

predicate TpcInit(s:TpcState, con:Constants)
{
    && WellFormedLConfiguration(con.config)
    // && WFLParameters(c.params)
    && s.constants == con
    && LEnvironment_Init(s.environment)
    && TpcMapsComplete(s)
    && (forall i :: 0 <= i < |con.config.node_ids| ==> LSchedulerInit(s.hosts[i], HostConstants(i, con)))
}


predicate TpcNextCommon(ps:TpcState, ps':TpcState)
{
  && TpcMapsComplete(ps)
  && TpcConstantsUnchanged(ps, ps')
  && LEnvironment_Next(ps.environment, ps'.environment)
}

predicate TpcNextOneHost(ps:TpcState, ps':TpcState, idx:int, ios:seq<TpcIo>)
{
    && TpcNextCommon(ps, ps')
    && 0 <= idx < |ps.constants.config.node_ids|
    && LSchedulerNext(ps.hosts[idx], ps'.hosts[idx], ios)
    && ps.environment.nextStep == LEnvStepHostIos(ps.constants.config.node_ids[idx], ios)
    && ps'.hosts == ps.hosts[idx := ps'.hosts[idx]]
}

predicate TpcNextEnvironment(s:TpcState, s':TpcState)
    ensures TpcNextEnvironment(s,s')==>forall p :: p in s'.environment.sentPackets ==> p in s.environment.sentPackets
{
    && TpcNextCommon(s, s')
    && !s.environment.nextStep.LEnvStepHostIos?
    && s'.hosts == s.hosts
}

// a replica send or receive a packet
predicate TpcNextOneExternal(s:TpcState, s':TpcState, eid:NodeIdentity, ios:seq<TpcIo>)
{
    && TpcNextCommon(s, s')
    && eid !in s.constants.config.node_ids
    && s.environment.nextStep == LEnvStepHostIos(eid, ios)
    && s'.hosts == s.hosts
}

predicate TpcNext(s:TpcState, s':TpcState)
{
    || (exists idx, ios :: TpcNextOneHost(s, s', idx, ios))
    || (exists eid, ios :: TpcNextOneExternal(s, s', eid, ios))
    || TpcNextEnvironment(s, s')
}
}