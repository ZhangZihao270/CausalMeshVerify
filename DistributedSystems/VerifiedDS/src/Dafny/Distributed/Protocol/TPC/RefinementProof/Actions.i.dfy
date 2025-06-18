include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Constants.i.dfy"

module TpcRefinement__Actions_i{
import opened LiveTPC__DistributedSystem_i
import opened LiveTPC__Host_i
import opened LiveTPC__Constants_i
import opened LiveTPC__Message_i
import opened Temporal__Temporal_s
import opened Environment_s
import opened TpcRefinement__Assumptions_i
import opened TpcRefinement__Constants_i

lemma lemma_ActionThatChangesHostIsThatHostsAction(
    b:Behavior<TpcState>,
    c:Constants,
    i:int,
    host_index:int
)
returns
(
    ios:seq<TpcIo>
)
    requires IsValidBehaviorPrefix(b, c, i+1)
    requires 0 <= i 
    requires 0 <= host_index < |b[i].hosts|
    requires 0 <= host_index < |b[i+1].hosts|
    requires b[i+1].hosts[host_index] != b[i].hosts[host_index]
    ensures b[i].environment.nextStep.LEnvStepHostIos?
    ensures 0 <= host_index < |c.config.node_ids|
    ensures b[i].environment.nextStep.actor == c.config.node_ids[host_index]
    ensures ios == b[i].environment.nextStep.ios
    ensures TpcNext(b[i], b[i+1])
    ensures TpcNextOneHost(b[i], b[i+1], host_index, ios)
{
    lemma_AssumptionsMakeValidTransition(b, c, i);
    lemma_ConstantsAllConsistent(b, c, i);
    assert TpcNext(b[i], b[i+1]);
    ios :| TpcNextOneHost(b[i], b[i+1], host_index, ios);
}
}