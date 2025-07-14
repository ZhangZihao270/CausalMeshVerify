include "../distributed_system.dfy"
// include "causalcut.dfy"
include "packet_sending.dfy"
include "properties.dfy"
// include "propagation_lemma.dfy"
include "propagation_lemma2.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module CausalMesh_Proof_PropagationLemma3_i {
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
// import opened CausalMesh_Proof_PropagationLemma_i
import opened CausalMesh_Proof_PropagationLemma2_i
import opened CausalMesh_Proof_PacketSending_i
import opened CausalMesh_Proof_Properties_i
// import opened CausalMesh_Proof_MessageReadReply_i
import opened Collections__Seqs_s
import opened Collections__Maps_i
import opened Collections__Maps2_s

lemma lemma_PropagationAtTail2(
    b:Behavior<CMState>,
    i:int,
    idx:int,
    p:Packet,
    ios:seq<CMIo>
)
    requires 0 < i 
    requires IsValidBehaviorPrefix(b, i)
    // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    requires CMNext(b[i-1], b[i])
    requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
    requires 0 <= idx < Nodes
    requires |ios| > 0
    requires ios[0].LIoOpReceive?
    requires p.msg.Message_Propagation?
    requires p in b[i-1].environment.sentPackets
    requires p.dst == idx
    requires idx == b[i-1].servers[idx].s.id
    requires ios[0].r == p
    requires PacketValid(p)
    requires p.msg.start == b[i-1].servers[idx].s.next
    requires p.msg.round == 2
    requires ReceivePropagate(b[i-1].servers[idx].s, b[i].servers[idx].s, p, ExtractSentPacketsFromIos(ios))
    ensures AllVersionsInDepsAreMetOnAllServers(b, i, p.msg.meta.deps)
{
    var p := ios[0].r;
    var s := b[i-1].servers[idx].s;
    var s' := b[i].servers[idx].s;

    assert p.msg.start == s.next;

    assert 0 <= i - 1;
    assert IsValidBehaviorPrefix(b, i-1);
    assert forall j :: 0 <= j < i-1 ==> CMNext(b[j], b[j+1]);
    // assert CMNext(b[i-2], b[i-1]);
    assert CMNext(b[i-1], b[i]);
    // assert CMNextCommon(b[i-1], b[i]);
    assert forall j :: 0 <= j < Nodes ==> ServerValid(b[i-1].servers[j].s);
    assert p.msg.Message_Propagation?;
    assert CMInit(b[0]);
    assert |b[i-1].servers| == Nodes;
    assert p in b[i-1].environment.sentPackets;
    assert PacketValid(p);

    assert p.dst == idx;
    assert idx == s.id;

    var nodes := lemma_Propagation2(b, i-1, p);
    assert |nodes| > 1;
    assert nodes[0] == p.msg.start;
    assert nodes[|nodes|-2] == p.src;
    assert nodes[|nodes|-1] == p.dst;
    assert forall j :: 0 <= j < |nodes| ==> 0 <= nodes[j] < Nodes;
    assert forall j :: 0 <= j < |nodes| - 1 ==> NodesAreNext(nodes[j], nodes[j+1]);
    assert forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i-1].servers[nodes[j]].s.icache, b[i-1].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc);
    assert forall j :: 0 <= j < |nodes| - 1 ==> DepsIsMet(b[i-1].servers[nodes[j]].s.icache, b[i-1].servers[nodes[j]].s.ccache, p.msg.meta.deps);

    lemma_ServerNextSatisfyNodesAreNext(s.id, s.next);
    assert NodesAreNext(s.id, p.msg.start);
    assert p.dst == s.id;
    lemma_NodesFormACircle(p.msg.start, p.dst, nodes);
    // assert forall j :: 0 <= j < Nodes ==> j in nodes;
    assert NodesAreComplete(nodes);

    var new_deps := p.msg.meta.deps;
    var (new_icache, new_ccache) := PullDeps2(s.icache, s.ccache, new_deps);
    

    var new_ccache' := InsertIntoCCache(new_ccache, p.msg.meta);
    var new_icache' := AddMetaToICache(new_icache, p.msg.meta);
    // reveal_DepsIsMet();
    lemma_AddMetaToCacheImpliesMetaIsMetInNewCache(new_icache, new_ccache, p.msg.meta);
    assert DepsIsMet(new_icache', new_ccache', p.msg.meta.deps);

    assert VCHappendsBefore(p.msg.meta.vc, new_ccache'[p.msg.key].vc) || VCEq(p.msg.meta.vc, new_ccache'[p.msg.key].vc);
    // reveal_DepsIsMet();
    // lemma_DepsIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, p.msg.meta.deps); // this could be proved, but may timeout
    
    lemma_AVersionOfAKeyIsMetIsTransitive(b, i, p.msg.key, p.msg.meta.vc, p.msg.meta.deps, nodes);
    // assert forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc);
    // assert forall j :: 0 <= j < |nodes| - 1 ==> DepsIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.meta.deps);
    // assert forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc);
    assert nodes[|nodes|-1] == idx;
    
    lemma_DepsIsMetForNodes(b, i, nodes, p.msg.meta.deps);

    assert |b[i].servers| == Nodes;
    assert forall j :: 0 <= j < Nodes ==> ServerValid(b[i].servers[j].s);
    assert |nodes| > 1;
    assert forall j :: 0 <= j < |nodes| ==> 0 <= nodes[j] < Nodes;
    // lemma_Nodes(nodes);
    // assert forall j :: 0 <= j < Nodes ==> j in nodes;
    lemma_DepsIsMetForAllNodes(b, i, nodes, p.msg.meta.deps);
    assert AllVersionsInDepsAreMetOnAllServers(b, i, p.msg.meta.deps);
}

predicate {:opaque} NodesAreComplete(
    nodes:seq<int>
)
{
    forall j :: 0 <= j < Nodes ==> j in nodes
}

lemma lemma_AddMetaToCacheImpliesMetaIsMetInNewCache(
    icache:ICache,
    ccache:CCache,
    meta:Meta
)
    requires ICacheValid(icache)
    requires CCacheValid(ccache)
    requires MetaValid(meta)
    requires forall k :: k in meta.deps ==> k in icache
    requires forall k :: k in Keys_domain ==> k in icache && k in ccache
    ensures var icache' := AddMetaToICache(icache, meta);
            var ccache' := InsertIntoCCache(ccache, meta);
            DepsIsMet(icache', ccache', meta.deps)
{
    reveal_DepsIsMet();
    lemma_ReceiveAPropagationImpliesTheDepsAreAlreadyMet(icache, ccache, meta.deps);

    var icache' := AddMetaToICache(icache, meta);
    var ccache' := InsertIntoCCache(ccache, meta);
    assert meta in icache'[meta.key];
    assert VCHappendsBefore(meta.vc, ccache'[meta.key].vc) || VCEq(meta.vc, ccache'[meta.key].vc);
    // assert forall k :: k in meta.deps ==> VCHappendsBefore(meta.deps[k], ccache'[k].vc) || VCEq(meta.deps[k], ccache'[k].vc);
    assert DepsIsMet(icache', ccache', meta.deps);
    // forall k | k in meta.deps 
    // {
    //     var vc := meta.deps[k];
    //     var m := FoldMetaSet2(ccache'[k], icache'[k]);
    //     assert VCEq(vc, m.vc) || VCHappendsBefore(vc, m.vc);
    // }
}


lemma lemma_ServerNextSatisfyNodesAreNext(id:int, next:int)
    requires 0 <= id < Nodes
    requires next == Circle(id, Nodes)
    ensures NodesAreNext(id, next)
{

}

lemma {:axiom} lemma_NodesFormACircle(start:int, end:int, nodes:seq<int>)
    requires 0 <= start < Nodes
    requires 0 <= end < Nodes
    requires |nodes| > 1
    requires nodes[0] == start
    requires nodes[|nodes|-1] == end
    requires forall j :: 0 <= j < |nodes| ==> 0 <= nodes[j] < Nodes
    requires forall j :: 0 <= j < |nodes| - 1 ==> NodesAreNext(nodes[j], nodes[j+1])
    requires NodesAreNext(end, start)
    // ensures forall j :: 0 <= j < Nodes ==> j in nodes
    ensures NodesAreComplete(nodes)


lemma lemma_DepsIsMetForNodes(
    b:Behavior<CMState>,
    i:int,
    nodes:seq<int>,
    deps:Dependency
)
    requires i > 0 
    requires IsValidBehaviorPrefix(b, i)
    requires |b[i].servers| == Nodes
    requires forall j :: 0 <= j < Nodes ==> ServerValid(b[i].servers[j].s)
    requires DependencyValid(deps)
    requires |nodes| > 1
    requires forall j :: 0 <= j < |nodes| ==> 0 <= nodes[j] < Nodes 
    requires forall j :: 0 <= j < |nodes| - 1 ==> DepsIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, deps)
    requires DepsIsMet(b[i].servers[nodes[|nodes|-1]].s.icache, b[i].servers[nodes[|nodes|-1]].s.ccache, deps)
    ensures forall j :: 0 <= j < |nodes| ==> DepsIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, deps)
{

}

// this one can be proved, but the last requires is not passed at the end of lemma_PropagationAtTail
// but this requires is ture, beacuse it can pass at the middle of lemma_PropagationAtTail
lemma lemma_DepsIsMetForAllNodes(
    b:Behavior<CMState>,
    i:int,
    nodes:seq<int>,
    deps:Dependency
)
    requires i > 0 
    requires IsValidBehaviorPrefix(b, i)
    // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    requires |b[i].servers| == Nodes
    requires forall j :: 0 <= j < Nodes ==> ServerValid(b[i].servers[j].s)
    requires DependencyValid(deps)
    requires |nodes| > 1
    requires forall j :: 0 <= j < |nodes| ==> 0 <= nodes[j] < Nodes 
    requires forall j :: 0 <= j < |nodes| ==> DepsIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, deps)
    // requires forall j :: 0 <= j < Nodes ==> j in nodes
    requires NodesAreComplete(nodes)
    ensures AllVersionsInDepsAreMetOnAllServers(b, i, deps)
{
    reveal_AllVersionsInDepsAreMetOnAllServers();
    reveal_DepsIsMet();
    reveal_NodesAreComplete();
    assert forall n :: n in nodes ==> DepsIsMet(b[i].servers[n].s.icache, b[i].servers[n].s.ccache, deps);
    assert |b[i].servers| == Nodes;
    assert forall j :: 0 <= j < |b[i].servers| ==> j in nodes;
    assert forall j :: 0 <= j < |b[i].servers| ==> DepsIsMet(b[i].servers[j].s.icache, b[i].servers[j].s.ccache, deps);
    assert AllVersionsInDepsAreMetOnAllServers(b, i, deps);
}

}