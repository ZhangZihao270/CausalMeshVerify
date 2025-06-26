include "../distributed_system.dfy"
// include "causalcut.dfy"
include "packet_sending.dfy"
include "properties.dfy"
include "propagation.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module CausalMesh_Proof_MetaIsMet_i {
import opened CausalMesh_Cache_i
import opened CausalMesh_Message_i
import opened CausalMesh_Types_i
import opened Environment_s
import opened CausalMesh_DistributedSystem_i
import opened CausalMesh_Properties_i
import opened CausalMesh_Proof_Actions_i
import opened Temporal__Temporal_s
import opened CausalMesh_proof_Assumptions_i
import opened CausalMesh_Proof_Constants_i
import opened CausalMesh_Proof_PropagationLemma_i
import opened CausalMesh_Proof_Propagation_i
import opened CausalMesh_Proof_PacketSending_i
import opened CausalMesh_Proof_Properties_i
// import opened CausalMesh_Proof_MessageReadReply_i
import opened Collections__Seqs_s
import opened Collections__Maps_i
import opened Collections__Maps2_s

lemma lemma_MetaIsMetImpliesItsDepsAreMet(
    b:Behavior<CMState>,
    i:int,
    meta:Meta
)
    requires 0 < i 
    requires IsValidBehaviorPrefix(b, i)
    requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    requires MetaValid(meta)
    requires AVersionIsMetOnAllServers(b, i, meta.key, meta.vc)
    requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
    ensures AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps)
{
     if i <= 1 {
        assert CMNext(b[i-1], b[i]);
        lemma_MetaIsMetImpliesItsDepsAreMetForIndexOne(b, i, meta);
        return;
    }

    assert 0 < i - 1;

    lemma_ConstantsAllConsistent(b, i-1);
    lemma_ConstantsAllConsistent(b, i);

    lemma_BehaviorValidImpliesOneStepValid(b, i);

    if AVersionIsMetOnAllServers(b, i-1, meta.key, meta.vc)
    {
        lemma_MetaIsMetImpliesItsDepsAreMet(b, i-1, meta);
        lemma_DepsAreMetAreTransitive(b, i, meta);
        return;
    }

    // var ios := lemma_ActionThatChangesServerIsThatServersAction(b, i, )
    
    // how to find the node that is the tail of propagation of meta?

    var ios:seq<CMIo>;
    var idx :| 0 <= idx < Nodes;

    assert CMNext(b[i-1], b[i]);
    assert 0 < i; 
    assert IsValidBehaviorPrefix(b, i);
    assert MetaValid(meta);
    assert 0 <= idx < Nodes;

    lemma_IosIsPropagationTail(b, i, idx, ios, meta);

    assert ReceivePropagate(b[i-1].servers[idx].s, b[i].servers[idx].s, ios[0].r, ExtractSentPacketsFromIos(ios));

    var p_pro := ios[0].r;
    assert p_pro.dst == idx;

    lemma_PropagationAtTail2(b, i, idx, p_pro, ios);
    assert AllVersionsInDepsAreMetOnAllServers(b, i, p_pro.msg.meta.deps);
    assert AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps);
}

lemma {:axiom} lemma_MetaIsMetImpliesItsDepsAreMetForIndexOne(
    b:Behavior<CMState>,
    i:int,
    meta:Meta
)
    requires i == 1 
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires MetaValid(meta)
    ensures !exists p :: p in b[i].environment.sentPackets && p.msg.Message_Propagation?
    ensures AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps)

lemma {:axiom} lemma_DepsAreMetAreTransitive(
    b:Behavior<CMState>,
    i:int,
    meta:Meta
)
    requires i > 1 
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires MetaValid(meta)
    requires AllVersionsInDepsAreMetOnAllServers(b, i-1, meta.deps)
    ensures AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps)
// {

// }

lemma {:axiom} lemma_IosIsPropagationTail(
    b:Behavior<CMState>,
    i:int,
    idx:int,
    ios:seq<CMIo>,
    meta:Meta
)
    requires 0 < i 
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires MetaValid(meta)
    requires 0 <= idx < Nodes
    ensures |ios| > 1
    ensures ios[0].LIoOpReceive?
    ensures ios[0].r.msg.Message_Propagation?
    ensures ios[0].r in b[i-1].environment.sentPackets
    ensures ReceivePropagate(b[i-1].servers[idx].s, b[i].servers[idx].s, ios[0].r, ExtractSentPacketsFromIos(ios))
    ensures ios[0].r.msg.start == b[i-1].servers[idx].s.next
    ensures ios[0].r.dst == idx
    ensures ios[0].r.msg.meta == meta
    // ensures forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
}