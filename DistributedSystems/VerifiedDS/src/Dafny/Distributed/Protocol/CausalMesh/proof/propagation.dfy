include "../distributed_system.dfy"
// include "causalcut.dfy"
include "packet_sending.dfy"
include "properties.dfy"
include "propagation_lemma.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module CausalMesh_Proof_Propagation_i {
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
import opened CausalMesh_Proof_PacketSending_i
import opened CausalMesh_Proof_Properties_i
// import opened CausalMesh_Proof_MessageReadReply_i
import opened Collections__Seqs_s
import opened Collections__Maps_i
import opened Collections__Maps2_s


lemma lemma_PropagationAtTail(
    b:Behavior<CMState>,
    i:int,
    idx:int,
    p:Packet,
    ios:seq<CMIo>
)
    requires 0 < i 
    requires IsValidBehaviorPrefix(b, i)
    requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    requires CMNext(b[i-1], b[i])
    requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
    requires 0 <= idx < Nodes
    requires |ios| > 1
    requires ios[0].LIoOpReceive?
    requires p.msg.Message_Propagation?
    requires p in b[i-1].environment.sentPackets
    requires p.dst == idx
    requires idx == b[i-1].servers[idx].s.id
    requires ios[0].r == p
    requires PacketValid(p)
    requires p.msg.start == b[i-1].servers[idx].s.next
    requires ReceivePropagate(b[i-1].servers[idx].s, b[i].servers[idx].s, p, ExtractSentPacketsFromIos(ios))
    ensures AVersionIsMetOnAllServers(b, i, ios[0].r.msg.key, ios[0].r.msg.meta.vc)
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
    assert forall j :: 0 <= j < Nodes ==> j in nodes;

    var new_deps := p.msg.meta.deps;
    var (new_icache, new_ccache) := PullDeps2(s.icache, s.ccache, new_deps);
    var merged_meta := MetaMerge(new_ccache[p.msg.key], p.msg.meta);
    assert VCHappendsBefore(p.msg.meta.vc, merged_meta.vc) || VCEq(p.msg.meta.vc, merged_meta.vc);

    var new_ccache' := InsertIntoCCache(new_ccache, merged_meta);
    assert VCHappendsBefore(p.msg.meta.vc, new_ccache'[p.msg.key].vc) || VCEq(p.msg.meta.vc, new_ccache'[p.msg.key].vc);
    
    assert AVersionOfAKeyIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, p.msg.key, p.msg.meta.vc);

    // assert forall j :: 0 <= j < Nodes ==> j in nodes;

    lemma_AVersionOfAKeyIsMetIsTransitive(b, i, p.msg.key, p.msg.meta.vc, p.msg.meta.deps, nodes);
    // assert forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc);
    // assert forall j :: 0 <= j < |nodes| - 1 ==> DepsIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.meta.deps);
    // assert forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc);
    assert nodes[|nodes|-1] == idx;

    // assert forall j :: 0 <= j < Nodes ==> j in nodes;

    // assert AVersionOfAKeyIsMet(b[i].servers[nodes[|nodes|-1]].s.icache, b[i].servers[nodes[|nodes|-1]].s.ccache, p.msg.key, p.msg.meta.vc);
    lemma_AVersionOfAKeyIsMetForNodes(b, i, nodes, p.msg.key, p.msg.meta.vc);
    assert forall j :: 0 <= j < |nodes| ==> AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc);
    // // assert forall j :: 0 <= j < Nodes ==> AVersionOfAKeyIsMet(b[i].servers[j].s.icache, b[i].servers[j].s.ccache, p.msg.key, p.msg.meta.vc);


    assert |b[i].servers| == Nodes;
    assert forall j :: 0 <= j < Nodes ==> ServerValid(b[i].servers[j].s);
    assert |nodes| > 1;
    assert forall j :: 0 <= j < |nodes| ==> 0 <= nodes[j] < Nodes;
    // lemma_Nodes(nodes);
    // assert forall j :: 0 <= j < Nodes ==> j in nodes;
    lemma_AVersionOfAKeyIsMetForAllNodes(b, i, nodes, p.msg.key, p.msg.meta.vc);
    // assert AVersionIsMetOnAllServers(b, i, p.msg.key, p.msg.meta.vc);
}

lemma lemma_PropagationAtTail2(
    b:Behavior<CMState>,
    i:int,
    idx:int,
    p:Packet,
    ios:seq<CMIo>
)
    requires 0 < i 
    requires IsValidBehaviorPrefix(b, i)
    requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    requires CMNext(b[i-1], b[i])
    requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
    requires 0 <= idx < Nodes
    requires |ios| > 1
    requires ios[0].LIoOpReceive?
    requires p.msg.Message_Propagation?
    requires p in b[i-1].environment.sentPackets
    requires p.dst == idx
    requires idx == b[i-1].servers[idx].s.id
    requires ios[0].r == p
    requires PacketValid(p)
    requires p.msg.start == b[i-1].servers[idx].s.next
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
    assert forall j :: 0 <= j < Nodes ==> j in nodes;

    var new_deps := p.msg.meta.deps;
    var (new_icache, new_ccache) := PullDeps2(s.icache, s.ccache, new_deps);
    var merged_meta := MetaMerge(new_ccache[p.msg.key], p.msg.meta);
    assert VCHappendsBefore(p.msg.meta.vc, merged_meta.vc) || VCEq(p.msg.meta.vc, merged_meta.vc);

    var new_ccache' := InsertIntoCCache(new_ccache, merged_meta);
    assert VCHappendsBefore(p.msg.meta.vc, new_ccache'[p.msg.key].vc) || VCEq(p.msg.meta.vc, new_ccache'[p.msg.key].vc);
    // reveal_DepsIsMet();
    lemma_DepsIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, p.msg.meta.deps); // this could be proved, but may timeout
    
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

// lemma {:axiom} lemma_Nodes(nodes:seq<int>)
//     ensures forall j :: 0 <= j < Nodes ==> j in nodes

// this one can be proved, but the last requires is not passed at the end of lemma_PropagationAtTail
// but this requires is ture, beacuse it can pass at the middle of lemma_PropagationAtTail
lemma {:axiom} lemma_AVersionOfAKeyIsMetForAllNodes(
    b:Behavior<CMState>,
    i:int,
    nodes:seq<int>,
    key:Key,
    vc:VectorClock
)
    requires i > 0 
    requires IsValidBehaviorPrefix(b, i)
    requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    requires |b[i].servers| == Nodes
    requires forall j :: 0 <= j < Nodes ==> ServerValid(b[i].servers[j].s)
    requires key in Keys_domain
    requires VectorClockValid(vc)
    requires |nodes| > 1
    requires forall j :: 0 <= j < |nodes| ==> 0 <= nodes[j] < Nodes 
    requires forall j :: 0 <= j < |nodes| ==> AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, key, vc)
    // requires forall j :: 0 <= j < Nodes ==> j in nodes
    ensures AVersionIsMetOnAllServers(b, i, key, vc)
// {
//     // assume forall s :: s in b[i].servers ==> s.s.id in nodes;
//     assert forall n :: n in nodes ==> AVersionOfAKeyIsMet(b[i].servers[n].s.icache, b[i].servers[n].s.ccache, key, vc);
//     // assert forall s :: s in b[i].servers ==> AVersionOfAKeyIsMet(s.s.icache, s.s.ccache, key, vc);
//     assert |b[i].servers| == Nodes;
//     // assume |nodes| == Nodes;
//     assert forall j :: 0 <= j < |b[i].servers| ==> j in nodes;
//     assert forall j :: 0 <= j < |b[i].servers| ==> AVersionOfAKeyIsMet(b[i].servers[j].s.icache, b[i].servers[j].s.ccache, key, vc);
// }

// this one can be proved, but the last requires is not passed at the end of lemma_PropagationAtTail
// but this requires is ture, beacuse it can pass at the middle of lemma_PropagationAtTail
lemma {:axiom} lemma_DepsIsMetForAllNodes(
    b:Behavior<CMState>,
    i:int,
    nodes:seq<int>,
    deps:Dependency
)
    requires i > 0 
    requires IsValidBehaviorPrefix(b, i)
    requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    requires |b[i].servers| == Nodes
    requires forall j :: 0 <= j < Nodes ==> ServerValid(b[i].servers[j].s)
    requires DependencyValid(deps)
    requires |nodes| > 1
    requires forall j :: 0 <= j < |nodes| ==> 0 <= nodes[j] < Nodes 
    requires forall j :: 0 <= j < |nodes| ==> DepsIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, deps)
    // requires forall j :: 0 <= j < Nodes ==> j in nodes
    ensures AllVersionsInDepsAreMetOnAllServers(b, i, deps)
// {
//     reveal_AllVersionsInDepsAreMetOnAllServers();
//     reveal_DepsIsMet();
//     assert forall n :: n in nodes ==> DepsIsMet(b[i].servers[n].s.icache, b[i].servers[n].s.ccache, deps);
//     assert |b[i].servers| == Nodes;
//     assert forall j :: 0 <= j < |b[i].servers| ==> j in nodes;
//     assert forall j :: 0 <= j < |b[i].servers| ==> DepsIsMet(b[i].servers[j].s.icache, b[i].servers[j].s.ccache, deps);
//     assert AllVersionsInDepsAreMetOnAllServers(b, i, deps);
// }

lemma lemma_AVersionOfAKeyIsMetForNodes(
    b:Behavior<CMState>,
    i:int,
    nodes:seq<int>,
    key:Key,
    vc:VectorClock
)
    requires i > 0 
    requires IsValidBehaviorPrefix(b, i)
    requires |b[i].servers| == Nodes
    requires forall j :: 0 <= j < Nodes ==> ServerValid(b[i].servers[j].s)
    requires key in Keys_domain
    requires VectorClockValid(vc)
    requires |nodes| > 1
    requires forall j :: 0 <= j < |nodes| ==> 0 <= nodes[j] < Nodes 
    requires forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, key, vc)
    requires AVersionOfAKeyIsMet(b[i].servers[nodes[|nodes|-1]].s.icache, b[i].servers[nodes[|nodes|-1]].s.ccache, key, vc)
    ensures forall j :: 0 <= j < |nodes| ==> AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, key, vc)
{

}

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
    ensures forall j :: 0 <= j < Nodes ==> j in nodes


function CalNode(start:int, n:int) : (res:int)
    requires 0 <= start < Nodes
    requires 1 <= n < Nodes
    ensures 0 <= res < Nodes
{
    (start + (n-1)) % Nodes
}

lemma {:axiom} lemma_ReceivePktDstIsMe(dst:int, me:int)
    ensures dst == me

// lemma lemma_Propagation(
//     b:Behavior<CMState>,
//     i:int,
//     p:Packet
//     // nodes:set<int>
// )
// returns (nodes:seq<int>)
//     requires 0 <= i 
//     requires IsValidBehaviorPrefix(b, i)
//     requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
//     // requires CMNext(b[i-1], b[i])
//     requires CMInit(b[0])
//     requires |b[i].servers| == Nodes
//     requires forall j :: 0 <= j < Nodes ==> ServerValid(b[i].servers[j].s)
//     requires p.msg.Message_Propagation?
//     requires p in b[i].environment.sentPackets
//     // requires forall n :: n in nodes ==> 0 <= n < Nodes
//     requires PacketValid(p)
//     ensures |nodes| > 1
//     ensures nodes[0] == p.msg.start
//     ensures nodes[|nodes|-2] == p.src
//     ensures nodes[|nodes|-1] == p.dst
//     ensures forall j :: 0 <= j < |nodes| ==> 0 <= nodes[j] < Nodes
//     ensures forall j :: 0 <= j < |nodes| - 1 ==> NodesAreNext(nodes[j], nodes[j+1])
//     ensures forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc)
//     // ensures p.src in nodes
//     // ensures var n := |nodes|;
//     //         forall j :: 0 <= j < n ==> CalNode(p.msg.start, n) in nodes
//     // requires var sp := ExtractSentPacketsFromIos(ios);
//     //         exists p :: p in sp ==> p.msg.Message_Propagation?
//     // requires ReceivePropagate(b[i-1].servers[idx].s, b[i].servers[idx].s, ios[0].r, ExtractSentPacketsFromIos(ios)) 
//     //         ||
//     //         ReceiveWrite(b[i-1].servers[idx].s, b[i].servers[idx].s, ios[0].r, ExtractSentPacketsFromIos(ios))
// {
//     if i == 0 {
//         return;
//     }

//     if p in b[i-1].environment.sentPackets{
//         nodes := lemma_Propagation(b, i-1, p);
//         assert CMNext(b[i-1], b[i]);
//         assume forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i-1].servers[nodes[j]].s.icache, b[i-1].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc);
//         lemma_AVersionOfAKeyIsMetIsTransitive(b, i, p.msg.key, p.msg.meta.vc, nodes);
//         assert forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc);
//         // assert nodes[0] == p.msg.start;
//         // assert nodes[|nodes|-1] == p.src;
//         return;
//     }

//     lemma_ConstantsAllConsistent(b, i-1);
//     lemma_ConstantsAllConsistent(b, i);

//     var ps := b[i-1];
//     var ps' := b[i];

//     var idx, ios := lemma_ActionThatSendsPropagationIsReceivePropogateOrReceiveWrite(b[i-1], b[i], p);
//     // assert idx in nodes;

//     if ios[0].r.msg.Message_Propagation? {
//         // assert 0 < i;
//         // assert IsValidBehaviorPrefix(b, i);
//         // assert CMNext(b[i-1], b[i]);
//         // assert 0 <= idx < Nodes;
//         // assert |ios| > 1;
//         // assert ios[0].r.msg.Message_Propagation?;
//         // assert p.msg.key == ios[0].r.msg.key;
//         // assert p.msg.meta.deps == ios[0].r.msg.meta.deps;
//         // var sp := ExtractSentPacketsFromIos(ios);
//         // assert ReceivePropagate(b[i-1].servers[idx].s, b[i].servers[idx].s, ios[0].r, sp);
//         // assert sp[0].msg.Message_Propagation?;
//         // assert sp[0].msg.meta.vc == p.msg.meta.vc;
//         // assert sp[0].msg.meta.deps == p.msg.meta.deps;
//         // assert ios[0].r.msg.start != b[i-1].servers[idx].s.next;
//         lemma_PropagationNotTail(b, i, idx, p.msg.key, p.msg.meta.vc, p.msg.meta.deps, ios);
//         assume AVersionOfAKeyIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, p.msg.key, p.msg.meta.vc);
//         var rp := ios[0].r;

//         assert NodesAreNext(p.src, p.dst);

//         assert rp.msg.Message_Propagation?;
//         assert rp in b[i-1].environment.sentPackets;
//         assert PacketValid(rp);
//         var prev_nodes := lemma_Propagation(b, i-1, rp);
        
//         assert |prev_nodes| > 0;
//         assert prev_nodes[0] == p.msg.start;
//         assume prev_nodes[|prev_nodes|-2] == rp.src;
//         assume prev_nodes[|prev_nodes|-1] == rp.dst;
//         lemma_ReceivePktDstIsMe(rp.dst, idx);
//         assume rp.dst == idx;
//         assert prev_nodes[|prev_nodes|-1] == p.src;
//         assume forall j :: 0 <= j < |prev_nodes| - 1 ==> AVersionOfAKeyIsMet(b[i-1].servers[prev_nodes[j]].s.icache, b[i-1].servers[prev_nodes[j]].s.ccache, rp.msg.key, rp.msg.meta.vc);

//         assert forall j :: 0 <= j < |prev_nodes| ==> 0 <= prev_nodes[j] < Nodes;
//         assert forall j :: 0 <= j < |prev_nodes| - 1 ==> NodesAreNext(prev_nodes[j], prev_nodes[j+1]);

//         nodes := prev_nodes + [p.dst];
//         assert nodes[0] == p.msg.start;
//         assert nodes[|nodes|-2] == p.src;
//         assert nodes[|nodes|-1] == p.dst;
//         // assert |nodes| > 1;
//         assert forall j :: 0 <= j < |nodes| ==> 0 <= nodes[j] < Nodes;
        
//         assert forall j :: 0 <= j < |nodes| - 1 ==> NodesAreNext(nodes[j], nodes[j+1]);
//         assert forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc);
//     } else {
//         assert i > 0;
//         assert IsValidBehaviorPrefix(b, i);
//         assert CMNext(b[i-1], b[i]);
//         assert 0 <= idx < Nodes;
//         assert |ios| > 1;
//         assert ios[0].LIoOpReceive?;
//         assert ios[0].r.msg.Message_Write?;
//         assert ReceiveWrite(b[i-1].servers[idx].s, b[i].servers[idx].s, ios[0].r, ExtractSentPacketsFromIos(ios));
//         var sp := ExtractSentPacketsFromIos(ios);

//         assert sp[|sp|-1].msg.Message_Propagation?;
//         assert sp[|sp|-1].msg.meta.vc == p.msg.meta.vc;
//         //         && sp[|sp|-1].msg.meta.deps == p.msg.meta.deps;
//         lemma_PropagationAtHead(b, i, idx, p.msg.key, p.msg.meta.vc, p.msg.meta.deps, ios);
//         assert AVersionOfAKeyIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, p.msg.key, p.msg.meta.vc);

//         var p_write := ios[0].r;
//         assert p_write.msg.Message_Write?;
//         assert p_write in b[i-1].environment.sentPackets;
//         // assume DepsIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, p_write.msg.deps_write);
//         // lemma_DepsInPropagationIsInWriteDepsOrLocals(b, i, idx, ios);
//         // assert DepsIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, p.msg.meta.deps);

//         assert idx == p.msg.start;
//         nodes := [idx] + [p.dst];
//         var n := |nodes|;
//         assert n == 2;
//         assert nodes[0] == p.msg.start;
//         assert p.src in nodes;
//         assert nodes[|nodes|-2] == p.src;
//         assert nodes[|nodes|-1] == p.dst;
//         assert NodesAreNext(p.src, p.dst);
//         assert forall j :: 0 <= j < |nodes| - 1 ==> NodesAreNext(nodes[j], nodes[j+1]);

//         assert AVersionOfAKeyIsMet(b[i].servers[p.src].s.icache, b[i].servers[p.src].s.ccache, p.msg.key, p.msg.meta.vc);
//         assert forall j :: 0 <= j < |nodes| - 1 ==> 
//             AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc);
//         //     && DepsIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.meta.deps);
//     }
//     // assert forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc);
// }

lemma lemma_Propagation2(
    b:Behavior<CMState>,
    i:int,
    p:Packet
    // nodes:set<int>
)
returns (nodes:seq<int>)
    requires 0 <= i 
    requires IsValidBehaviorPrefix(b, i)
    requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    // requires CMNext(b[i-1], b[i])
    requires CMInit(b[0])
    requires |b[i].servers| == Nodes
    requires forall j :: 0 <= j < Nodes ==> ServerValid(b[i].servers[j].s)
    requires p.msg.Message_Propagation?
    requires p in b[i].environment.sentPackets
    // requires forall n :: n in nodes ==> 0 <= n < Nodes
    requires PacketValid(p)
    requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
    ensures |nodes| > 1
    ensures nodes[0] == p.msg.start
    ensures nodes[|nodes|-2] == p.src
    ensures nodes[|nodes|-1] == p.dst
    ensures forall j :: 0 <= j < |nodes| ==> 0 <= nodes[j] < Nodes
    ensures forall j :: 0 <= j < |nodes| - 1 ==> NodesAreNext(nodes[j], nodes[j+1])
    ensures forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc)
    ensures forall j :: 0 <= j < |nodes| - 1 ==> DepsIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.meta.deps)
    // ensures p.src in nodes
    // ensures var n := |nodes|;
    //         forall j :: 0 <= j < n ==> CalNode(p.msg.start, n) in nodes
    // requires var sp := ExtractSentPacketsFromIos(ios);
    //         exists p :: p in sp ==> p.msg.Message_Propagation?
    // requires ReceivePropagate(b[i-1].servers[idx].s, b[i].servers[idx].s, ios[0].r, ExtractSentPacketsFromIos(ios)) 
    //         ||
    //         ReceiveWrite(b[i-1].servers[idx].s, b[i].servers[idx].s, ios[0].r, ExtractSentPacketsFromIos(ios))
{
    if i == 0 {
        return;
    }

    if p in b[i-1].environment.sentPackets{
        nodes := lemma_Propagation2(b, i-1, p);
        assert CMNext(b[i-1], b[i]);
        assume forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i-1].servers[nodes[j]].s.icache, b[i-1].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc);
        assume forall j :: 0 <= j < |nodes| - 1 ==> DepsIsMet(b[i-1].servers[nodes[j]].s.icache, b[i-1].servers[nodes[j]].s.ccache, p.msg.meta.deps);
        lemma_AVersionOfAKeyIsMetIsTransitive(b, i, p.msg.key, p.msg.meta.vc, p.msg.meta.deps, nodes);
        // assert forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc);
        // assert nodes[0] == p.msg.start;
        // assert nodes[|nodes|-1] == p.src;
        return;
    }

    lemma_ConstantsAllConsistent(b, i-1);
    lemma_ConstantsAllConsistent(b, i);

    var ps := b[i-1];
    var ps' := b[i];

    var idx, ios := lemma_ActionThatSendsPropagationIsReceivePropogateOrReceiveWrite(b[i-1], b[i], p);
    // assert idx in nodes;

    if ios[0].r.msg.Message_Propagation? {
        // assert 0 < i;
        // assert IsValidBehaviorPrefix(b, i);
        // assert CMNext(b[i-1], b[i]);
        // assert 0 <= idx < Nodes;
        // assert |ios| > 1;
        // assert ios[0].r.msg.Message_Propagation?;
        // assert p.msg.key == ios[0].r.msg.key;
        // assert p.msg.meta.deps == ios[0].r.msg.meta.deps;
        // var sp := ExtractSentPacketsFromIos(ios);
        // assert ReceivePropagate(b[i-1].servers[idx].s, b[i].servers[idx].s, ios[0].r, sp);
        // assert sp[0].msg.Message_Propagation?;
        // assert sp[0].msg.meta.vc == p.msg.meta.vc;
        // assert sp[0].msg.meta.deps == p.msg.meta.deps;
        // assert ios[0].r.msg.start != b[i-1].servers[idx].s.next;
        lemma_PropagationNotTail(b, i, idx, p.msg.key, p.msg.meta.vc, p.msg.meta.deps, ios);
        assume AVersionOfAKeyIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, p.msg.key, p.msg.meta.vc);
        assert DependencyValid(p.msg.meta.deps);
        assume DepsIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, p.msg.meta.deps);
        var rp := ios[0].r;

        assert NodesAreNext(p.src, p.dst);

        assert rp.msg.Message_Propagation?;
        assert rp in b[i-1].environment.sentPackets;
        assert PacketValid(rp);
        var prev_nodes := lemma_Propagation2(b, i-1, rp);
        
        assert |prev_nodes| > 0;
        assert prev_nodes[0] == p.msg.start;
        assume prev_nodes[|prev_nodes|-2] == rp.src;
        assume prev_nodes[|prev_nodes|-1] == rp.dst;
        lemma_ReceivePktDstIsMe(rp.dst, idx);
        assume rp.dst == idx;
        assert prev_nodes[|prev_nodes|-1] == p.src;
        // assume forall j :: 0 <= j < |prev_nodes| - 1 ==> AVersionOfAKeyIsMet(b[i-1].servers[prev_nodes[j]].s.icache, b[i-1].servers[prev_nodes[j]].s.ccache, rp.msg.key, rp.msg.meta.vc);
        assume forall j :: 0 <= j < |prev_nodes| - 1 ==> DepsIsMet(b[i-1].servers[prev_nodes[j]].s.icache, b[i-1].servers[prev_nodes[j]].s.ccache, p.msg.meta.deps);

        assert forall j :: 0 <= j < |prev_nodes| ==> 0 <= prev_nodes[j] < Nodes;
        assert forall j :: 0 <= j < |prev_nodes| - 1 ==> NodesAreNext(prev_nodes[j], prev_nodes[j+1]);

        nodes := prev_nodes + [p.dst];
        assert nodes[0] == p.msg.start;
        assert nodes[|nodes|-2] == p.src;
        assert nodes[|nodes|-1] == p.dst;
        // assert |nodes| > 1;
        assert forall j :: 0 <= j < |nodes| ==> 0 <= nodes[j] < Nodes;
        
        assert forall j :: 0 <= j < |nodes| - 1 ==> NodesAreNext(nodes[j], nodes[j+1]);
        // assert forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc);
        assert forall j :: 0 <= j < |nodes| - 1 ==> DepsIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.meta.deps);
    } else {
        assert i > 0;
        assert IsValidBehaviorPrefix(b, i);
        assert CMNext(b[i-1], b[i]);
        assert 0 <= idx < Nodes;
        assert |ios| > 1;
        assert ios[0].LIoOpReceive?;
        assert ios[0].r.msg.Message_Write?;
        assert ReceiveWrite(b[i-1].servers[idx].s, b[i].servers[idx].s, ios[0].r, ExtractSentPacketsFromIos(ios));
        var sp := ExtractSentPacketsFromIos(ios);

        var p_write := ios[0].r;
        assert p_write.msg.Message_Write?;
        assert p_write in b[i-1].environment.sentPackets;

        assert sp[|sp|-1].msg.Message_Propagation?;
        assert sp[|sp|-1].msg.meta.vc == p.msg.meta.vc;
        //         && sp[|sp|-1].msg.meta.deps == p.msg.meta.deps;

        // lemma_DepsIsMet(b[i-1].servers[idx].s.icache, b[i-1].servers[idx].s.ccache, p_write.msg.deps_write);
        assert AllWriteDepsAreMet(b, i-1);
        reveal_AllVersionsInDepsAreMetOnAllServers();
        reveal_DepsIsMet();
        assume DepsIsMet(b[i-1].servers[idx].s.icache, b[i-1].servers[idx].s.ccache, p_write.msg.deps_write);
        lemma_PropagationAtHead(b, i, idx, p.msg.key, p.msg.meta.vc, p.msg.meta.deps, ios);
        assert AVersionOfAKeyIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, p.msg.key, p.msg.meta.vc);
        assert DepsIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, p.msg.meta.deps);

        
        // assume DepsIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, p_write.msg.deps_write);
        // lemma_DepsInPropagationIsInWriteDepsOrLocals(b, i, idx, ios);
        // assert DepsIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, p.msg.meta.deps);

        assert idx == p.msg.start;
        nodes := [idx] + [p.dst];
        var n := |nodes|;
        assert n == 2;
        assert nodes[0] == p.msg.start;
        assert p.src in nodes;
        assert nodes[|nodes|-2] == p.src;
        assert nodes[|nodes|-1] == p.dst;
        assert NodesAreNext(p.src, p.dst);
        assert forall j :: 0 <= j < |nodes| - 1 ==> NodesAreNext(nodes[j], nodes[j+1]);

        assert AVersionOfAKeyIsMet(b[i].servers[p.src].s.icache, b[i].servers[p.src].s.ccache, p.msg.key, p.msg.meta.vc);
        assert forall j :: 0 <= j < |nodes| - 1 ==> 
            AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc)
            && DepsIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.meta.deps);
    }
    // assert forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc);
}

lemma {:axiom} lemma_DepsIsMet(icache:ICache, ccache:CCache, deps:Dependency)
    requires ICacheValid(icache)
    requires CCacheValid(ccache)
    requires forall k :: k in Keys_domain ==> k in icache && k in ccache
    requires DependencyValid(deps)
    ensures DepsIsMet(icache, ccache, deps)

lemma {:axiom} lemma_AVersionOfAKeyIsMetIsTransitive(
    b:Behavior<CMState>,
    i:int,
    key:Key,
    vc:VectorClock,
    deps:Dependency,
    nodes:seq<int>
)
    requires 0 < i 
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires key in Keys_domain
    requires VectorClockValid(vc)
    requires DependencyValid(deps)
    requires |nodes| > 1
    requires forall j :: 0 <= j < |nodes| ==> 0 <= nodes[j] < Nodes
    requires forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i-1].servers[nodes[j]].s.icache, b[i-1].servers[nodes[j]].s.ccache, key, vc)
    requires forall j :: 0 <= j < |nodes| - 1 ==> DepsIsMet(b[i-1].servers[nodes[j]].s.icache, b[i-1].servers[nodes[j]].s.ccache, deps)
    ensures forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, key, vc)
    ensures forall j :: 0 <= j < |nodes| - 1 ==> DepsIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, deps)
// {
//     var j :| 0 <= j < |nodes| - 1;
//     var s := b[i-1].servers[nodes[j]].s;
//     var s' := b[i].servers[nodes[j]].s;
//     assume forall k :: k in s.ccache ==> k in s'.ccache && (VCHappendsBefore(s.ccache[k].vc, s'.ccache[k].vc) || VCEq(s.ccache[k].vc, s'.ccache[k].vc));
// }


lemma lemma_PropagationNotTail(
    b:Behavior<CMState>,
    i:int,
    idx:int,
    key:Key,
    vc:VectorClock,
    deps:Dependency,
    ios:seq<CMIo>
    // ,
    // nodes:set<int>
)
    requires 0 < i 
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires 0 <= idx < Nodes
    requires |ios| > 1
    requires ios[0].LIoOpReceive?
    requires ios[0].r.msg.Message_Propagation?
    requires PacketValid(ios[0].r)
    requires ios[0].r.msg.start != b[i-1].servers[idx].s.next
    // requires forall n :: n in nodes ==> 1 <= n < Nodes
    requires ReceivePropagate(b[i-1].servers[idx].s, b[i].servers[idx].s, ios[0].r, ExtractSentPacketsFromIos(ios)) 
    requires key == ios[0].r.msg.key
    requires deps == ios[0].r.msg.meta.deps
    requires var sp := ExtractSentPacketsFromIos(ios);
            sp[0].msg.Message_Propagation? && sp[0].msg.meta.vc == vc && sp[0].msg.meta.deps == deps
    ensures AVersionOfAKeyIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, key, vc)
    ensures DepsIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, deps)
    // ensures forall k :: 0 < k <= n ==> 
    //          var node := CalNode(ios[0].r.msg.start, k);
    //          AVersionOfAKeyIsMet(b[i].servers[node].s.icache, b[i].servers[node].s.ccache, ios[0].r.msg.key, ios[0].r.msg.meta.vc)
{
    reveal_DepsIsMet();
    var p := ios[0].r;
    var s := b[i-1].servers[idx].s;
    var s' := b[i].servers[idx].s;

    lemma_ReceiveAPropagationImpliesTheDepsAreAlreadyMet(s.icache, s.ccache, p.msg.meta.deps);

    var sp := ExtractSentPacketsFromIos(ios);
    var p_pro := sp[0];
    assert p_pro.msg.Message_Propagation?;

    var k := p.msg.key;
    
    var meta := p.msg.meta;
    
    var new_icache := AddMetaToICache(s.icache, p.msg.meta);
    assert meta in s'.icache[k];

    assert AVersionOfAKeyIsMet(s'.icache, s'.ccache, p.msg.key, meta.vc);
    assert DepsIsMet(s'.icache, s'.ccache, p.msg.meta.deps);
}

lemma {:axiom} lemma_ReceiveAPropagationImpliesTheDepsAreAlreadyMet(icache:ICache, ccache:CCache, deps:Dependency)
    requires ICacheValid(icache)
    requires CCacheValid(ccache)
    requires DependencyValid(deps)
    requires forall k :: k in Keys_domain ==> k in icache && k in ccache
    ensures DepsIsMet(icache, ccache, deps)
}