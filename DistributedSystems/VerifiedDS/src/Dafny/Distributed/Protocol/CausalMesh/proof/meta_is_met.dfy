include "../distributed_system.dfy"
// include "causalcut.dfy"
include "packet_sending.dfy"
include "properties.dfy"
include "propagation.dfy"
include "propagation_lemma3.dfy"
include "always_met.dfy"
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
import opened CausalMesh_Proof_PropagationLemma3_i
import opened CausalMesh_Proof_Propagation_i
import opened CausalMesh_Proof_PacketSending_i
import opened CausalMesh_Proof_Properties_i
import opened CausalMesh_Proof_AllwaysMet_i
// import opened CausalMesh_Proof_MessageReadReply_i
import opened Collections__Seqs_s
import opened Collections__Maps_i
import opened Collections__Maps2_s

// lemma lemma_MetaIsMetImpliesItsDepsAreMet(
//     b:Behavior<CMState>,
//     i:int,
//     meta:Meta
// )
//     requires 0 < i 
//     requires IsValidBehaviorPrefix(b, i)
//     // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
//     requires MetaValid(meta)
//     requires AVersionIsMetOnAllServers(b, i, meta.key, meta.vc)
//     requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
//     requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
//     ensures AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps)
// {
//     if i == 0 {
//         return;
//     }

//     if i == 1 {
//         lemma_BehaviorValidImpliesOneStepValid(b, i);
//         assert CMNext(b[i-1], b[i]);
//         lemma_MetaIsMetImpliesItsDepsAreMetForIndexOne(b, i, meta);
//         // reveal_AllVersionsInDepsAreMetOnAllServers();
//         assert AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps);
//         return;
//     }

//     assert 0 < i - 1;

//     lemma_ConstantsAllConsistent(b, i-1);
//     lemma_ConstantsAllConsistent(b, i);

//     lemma_BehaviorValidImpliesOneStepValid(b, i);

//     if AVersionIsMetOnAllServers(b, i-1, meta.key, meta.vc)
//     {
//         lemma_MetaIsMetImpliesItsDepsAreMet(b, i-1, meta);
//         assume ServerNextDoesNotDecreaseVersions(b[i-1], b[i]);
//         assert i > 1;
//         assert IsValidBehaviorPrefix(b, i);
//         assert CMNext(b[i-1], b[i]);
//         assert DependencyValid(meta.deps);
//         assume AllVersionsInDepsAreMetOnAllServers(b, i-1, meta.deps);
//         lemma_AllVersionsInDepsAreMetOnAllServersWillAlwaysMet(b, i, meta.deps);
//         return;
//     }

//     // var ios := lemma_ActionThatChangesServerIsThatServersAction(b, i, )
    
//     // how to find the node that is the tail of propagation of meta?

//     var ios:seq<CMIo>;
//     var idx :| 0 <= idx < Nodes;

//     assert CMNext(b[i-1], b[i]);
//     assert 0 < i; 
//     assert IsValidBehaviorPrefix(b, i);
//     assert MetaValid(meta);
//     assert 0 <= idx < Nodes;

//     lemma_IosIsPropagationTail(b, i, idx, ios, meta);

//     assert ReceivePropagate(b[i-1].servers[idx].s, b[i].servers[idx].s, ios[0].r, ExtractSentPacketsFromIos(ios));

//     var p_pro := ios[0].r;
//     assert p_pro.dst == idx;

//     lemma_PropagationAtTail2(b, i, idx, p_pro, ios);
//     assert AllVersionsInDepsAreMetOnAllServers(b, i, p_pro.msg.meta.deps);
//     assert AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps);
// }

// lemma lemma_MetaIsMetImpliesItsDepsAreMet2(
//     b:Behavior<CMState>,
//     i:int,
//     idx:int,
//     meta:Meta
// )
//     requires 0 < i 
//     requires IsValidBehaviorPrefix(b, i)
//     requires CMNext(b[i-1], b[i])
//     requires 0 <= idx < Nodes
//     requires MetaValid(meta)
//     requires AVersionOfAKeyIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, meta.key, meta.vc)
//     // requires meta in b[i].servers[idx].s.icache[meta.key]
//     // requires meta != EmptyMeta(meta.key)
//     // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    
//     requires AVersionIsMetOnAllServers(b, i, meta.key, meta.vc)
//     requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
//     requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
//     ensures AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps)
// {
//     if i == 0 {
//         return;
//     }

//     if i == 1 {
//         lemma_BehaviorValidImpliesOneStepValid(b, i);
//         assert CMNext(b[i-1], b[i]);
//         lemma_MetaIsMetImpliesItsDepsAreMetForIndexOne2(b, i);
//         // reveal_AllVersionsInDepsAreMetOnAllServers();
//         // assert AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps);
//         assert b[i].servers[idx].s.icache == InitICache();
//         assert b[i].servers[idx].s.ccache == InitCCache();
//         if meta != EmptyMeta(meta.key){
//             if VCHappendsBefore(EmptyMeta(meta.key).vc, meta.vc) {
//                 assert meta !in b[i].servers[idx].s.icache[meta.key];
//                 assert !(VCHappendsBefore(meta.vc, b[i].servers[idx].s.ccache[meta.key].vc) || VCEq(meta.vc, b[i].servers[idx].s.ccache[meta.key].vc));
//                 var m := FoldMetaSet2(b[i].servers[idx].s.ccache[meta.key], b[i].servers[idx].s.icache[meta.key]);
//                 assert b[i].servers[idx].s.ccache[meta.key] == EmptyMeta(meta.key);
//                 assert forall m :: m in b[i].servers[idx].s.icache[meta.key] ==> m == EmptyMeta(meta.key);
//                 lemma_FoldEmptyMetasResultInEmptyMeta(b[i].servers[idx].s.ccache[meta.key], b[i].servers[idx].s.icache[meta.key]);
//                 assert m == EmptyMeta(meta.key);
//                 assert !AVersionOfAKeyIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, meta.key, meta.vc);
//                 assert false;
//             } else {
//                 lemma_MetaWithNonEmptyDepsImpliesTheVCLargerThanZero(meta);
//                 assert meta !in b[i].servers[idx].s.icache[meta.key];
//                 assert !(VCHappendsBefore(meta.vc, b[i].servers[idx].s.ccache[meta.key].vc) || VCEq(meta.vc, b[i].servers[idx].s.ccache[meta.key].vc));
//                 var m := FoldMetaSet2(b[i].servers[idx].s.ccache[meta.key], b[i].servers[idx].s.icache[meta.key]);
//                 assert b[i].servers[idx].s.ccache[meta.key] == EmptyMeta(meta.key);
//                 assert forall m :: m in b[i].servers[idx].s.icache[meta.key] ==> m == EmptyMeta(meta.key);
//                 lemma_FoldEmptyMetasResultInEmptyMeta(b[i].servers[idx].s.ccache[meta.key], b[i].servers[idx].s.icache[meta.key]);
//                 assert m == EmptyMeta(meta.key);
//                 assert !AVersionOfAKeyIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, meta.key, meta.vc);
//                 assert false;
//             }
//         } 
//         else {
//             reveal_AllVersionsInDepsAreMetOnAllServers();
//             assert AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps);
//         }
//         return;
//     }

//     assert 0 < i - 1;

//     lemma_ConstantsAllConsistent(b, i-1);
//     lemma_ConstantsAllConsistent(b, i);

//     lemma_BehaviorValidImpliesOneStepValid(b, i);

//     if AVersionIsMetOnAllServers(b, i-1, meta.key, meta.vc)
//     {
//         // assume meta in b[i-1].servers[idx].s.icache[meta.key];
//         lemma_MetaIsMetImpliesItsDepsAreMet2(b, i-1, idx, meta);
//         assume ServerNextDoesNotDecreaseVersions(b[i-1], b[i]);
//         assert i > 1;
//         assert IsValidBehaviorPrefix(b, i);
//         assert CMNext(b[i-1], b[i]);
//         assert DependencyValid(meta.deps);
//         assume AllVersionsInDepsAreMetOnAllServers(b, i-1, meta.deps);
//         lemma_AllVersionsInDepsAreMetOnAllServersWillAlwaysMet(b, i, meta.deps);
//         return;
//     }

//     // var ios := lemma_ActionThatChangesServerIsThatServersAction(b, i, )
    
//     // how to find the node that is the tail of propagation of meta?

//     var ios:seq<CMIo>;
//     var idx :| 0 <= idx < Nodes;

//     assert CMNext(b[i-1], b[i]);
//     assert 0 < i; 
//     assert IsValidBehaviorPrefix(b, i);
//     assert MetaValid(meta);
//     assert 0 <= idx < Nodes;

//     lemma_IosIsPropagationTail(b, i, idx, ios, meta);

//     assert ReceivePropagate(b[i-1].servers[idx].s, b[i].servers[idx].s, ios[0].r, ExtractSentPacketsFromIos(ios));

//     var p_pro := ios[0].r;
//     assert p_pro.dst == idx;

//     lemma_PropagationAtTail2(b, i, idx, p_pro, ios);
//     assert AllVersionsInDepsAreMetOnAllServers(b, i, p_pro.msg.meta.deps);
//     assert AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps);
// }

// lemma {:axiom} lemma_MetaIsMetImpliesItsDepsAreMetForIndexOne(
//     b:Behavior<CMState>,
//     i:int
//     ,
//     meta:Meta
// )
//     requires i == 1 
//     requires IsValidBehaviorPrefix(b, i)
//     requires CMNext(b[i-1], b[i])
//     requires MetaValid(meta)
//     ensures !exists p :: p in b[i].environment.sentPackets && p.msg.Message_Propagation?
//     ensures AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps)
// // {
// //     assert CMNext(b[i-1], b[i]);
// // }

lemma lemma_MetaIsMetImpliesItsDepsAreMetForIndexOne2(
    b:Behavior<CMState>,
    i:int
)
    requires i == 1 
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    // requires 0 <= idx < Nodes
    // requires meta in b[i].servers[idx].s.icache[meta.key]
    // requires MetaValid(meta)
    ensures !exists p :: p in b[i].environment.sentPackets && p.msg.Message_Propagation?
    // ensures AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps)
{
    assert CMNext(b[i-1], b[i]);
}

// lemma {:axiom} lemma_IosIsPropagationTail(
//     b:Behavior<CMState>,
//     i:int,
//     idx:int,
//     ios:seq<CMIo>,
//     meta:Meta
// )
//     requires 0 < i 
//     requires IsValidBehaviorPrefix(b, i)
//     requires CMNext(b[i-1], b[i])
//     requires MetaValid(meta)
//     requires 0 <= idx < Nodes
//     ensures |ios| > 1
//     ensures ios[0].LIoOpReceive?
//     ensures ios[0].r.msg.Message_Propagation?
//     ensures ios[0].r in b[i-1].environment.sentPackets
//     ensures ReceivePropagate(b[i-1].servers[idx].s, b[i].servers[idx].s, ios[0].r, ExtractSentPacketsFromIos(ios))
//     ensures ios[0].r.msg.start == b[i-1].servers[idx].s.next
//     ensures ios[0].r.msg.round == 2
//     ensures ios[0].r.dst == idx
//     ensures ios[0].r.msg.meta == meta
//     // ensures forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)

// lemma {:axiom} lemma_MetaIsMetImpliesAllPreviousMetasAreMet(
//     b:Behavior<CMState>,
//     i:int,
//     meta:Meta,
//     meta2:Meta
// )
//     requires i > 0
//     requires IsValidBehaviorPrefix(b, i)
//     requires MetaValid(meta)
//     requires MetaValid(meta2)
//     requires AVersionIsMetOnAllServers(b, i, meta.key, meta.vc)
//     requires VCHappendsBefore(meta2.vc, meta.vc) || VCEq(meta2.vc, meta.vc)
//     ensures AVersionIsMetOnAllServers(b, i, meta2.key, meta2.vc)

lemma lemma_AVersionIsPropagatedImpliesAllPreviousDepsAreMet(
    b:Behavior<CMState>,
    i:int,
    vc:VectorClock,
    deps:Dependency
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    requires VectorClockValid(vc)
    requires DependencyValid(deps)
    requires forall k :: k in deps ==> VCHappendsBefore(deps[k], vc) || VCEq(deps[k], vc)
    ensures AllVersionsInDepsAreMetOnAllServers(b, i, deps)
{
    reveal_AllVersionsInDepsAreMetOnAllServers();
    forall k | k in deps 
        ensures AVersionIsMetOnAllServers(b, i, k, deps[k])
    {
        assert VCHappendsBefore(deps[k], vc) || VCEq(deps[k], vc);
        lemma_AVersionIsPropagatedImpliesAllPreviousVersionsAreMet(b, i, vc, k, deps[k]);
        assert AVersionIsMetOnAllServers(b, i, k, deps[k]);
    }
}

lemma {:axiom} lemma_AVersionIsPropagatedImpliesAllPreviousVersionsAreMet(
    b:Behavior<CMState>,
    i:int,
    vc:VectorClock,
    key:Key,
    vc2:VectorClock
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    requires VectorClockValid(vc2)
    requires VectorClockValid(vc)
    requires key in Keys_domain
    requires VCHappendsBefore(vc2, vc) || VCEq(vc2, vc)
    ensures AVersionIsMetOnAllServers(b, i, key, vc2)
}