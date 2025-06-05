include "../DistributedSystem.i.dfy"
include "../../../Common/Logic/Temporal/Rules.i.dfy"
include "Assumptions.i.dfy"

module TpcRefinement__Constants_i {
import opened LiveTPC__DistributedSystem_i
import opened LiveTPC__Constants_i
import opened Temporal__Temporal_s
import opened Temporal__Rules_i
import opened Temporal__Heuristics_i
import opened TpcRefinement__Assumptions_i
import opened Collections__Maps2_s

predicate ConstantsAllConsistentInv(ps:TpcState)
{
    && |ps.constants.config.node_ids| == |ps.hosts|
    && forall idx :: 0 <= idx < |ps.constants.config.node_ids| ==>
        var s := ps.hosts[idx].host;
        && s.constants.my_index == idx
        && s.constants.all == ps.constants
        && s.coordinator.constants == s.constants
        && s.participant.constants == s.constants
}

lemma lemma_AssumptionsMakeValidTransition(
    b:Behavior<TpcState>,
    c:Constants,
    i:int
)
    requires IsValidBehaviorPrefix(b,c,i+1)
    requires 0 <= i 
    ensures TpcNext(b[i], b[i+1])
{
}

lemma lemma_ConstantsAllConsistent(
    b:Behavior<TpcState>,
    c:Constants,
    i:int
)
    requires IsValidBehaviorPrefix(b, c, i)
    requires 0 <= i 
    ensures b[i].constants == c 
    ensures ConstantsAllConsistentInv(b[i])
{
    TemporalAssist();

    if i > 0 
    {
        lemma_ConstantsAllConsistent(b, c, i-1);
        lemma_AssumptionsMakeValidTransition(b, c, i-1);
    }
}

lemma lemma_HostConstantsAllConsistent(
    b:Behavior<TpcState>,
    c:Constants,
    i:int,
    idx:int
)
    requires IsValidBehaviorPrefix(b, c, i)
    requires 0 <= i 
    requires 0 <= idx < |b[i].hosts| || 0 <= idx < |c.config.node_ids| || 0 <= idx < |b[i].constants.config.node_ids|
    ensures b[i].constants == c
    ensures |b[i].constants.config.node_ids| == |b[i].hosts|
    ensures var s := b[i].hosts[idx].host;
            && s.constants.my_index == idx
            && s.constants.all == b[i].constants
            && s.coordinator.constants == s.constants
            && s.participant.constants == s.constants
{
    lemma_ConstantsAllConsistent(b, c, i);
}
}