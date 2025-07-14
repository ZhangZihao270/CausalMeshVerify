include "../distributed_system.dfy"
// include "causalcut.dfy"
include "packet_sending.dfy"
include "properties.dfy"
// include "deps_are_met.dfy"
// include "monotonic_read.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module CausalMesh_Proof_AllwaysMet_i {
import opened CausalMesh_Cache_i
import opened CausalMesh_Message_i
import opened CausalMesh_Types_i
import opened Environment_s
import opened CausalMesh_DistributedSystem_i
import opened CausalMesh_Properties_i
import opened CausalMesh_PullDeps_i
import opened CausalMesh_Proof_Actions_i
import opened Temporal__Temporal_s
import opened CausalMesh_proof_Assumptions_i
import opened CausalMesh_Proof_Constants_i
import opened CausalMesh_Proof_PacketSending_i
import opened CausalMesh_Proof_Properties_i
// import opened CausalMesh_Proof_DepsAreMet_i
// import opened CausalMesh_Proof_Monotonic_Read_i
// import opened CausalMesh_Proof_Environment_i
import opened Collections__Seqs_s
import opened Collections__Maps_i
import opened Collections__Maps2_s

lemma {:axiom} lemma_AVersionIsMetWillAlwaysMet(
    i1:ICache,
    i2:ICache,
    c1:CCache,
    c2:CCache,
    k:Key,
    vc:VectorClock
)
    requires ICacheValid(i1)
    requires ICacheValid(i2)
    requires CCacheValid(c1)
    requires CCacheValid(c2)
    requires ICacheDoesNotDecrease(i1, i2)
    requires CCacheDoesNotDecrease(c1, c2)
    requires forall k :: k in Keys_domain ==> k in i1 && k in i2 && k in c1 && k in c2
    requires k in Keys_domain
    requires VectorClockValid(vc)
    requires AVersionOfAKeyIsMet(i1, c1, k, vc)
    ensures AVersionOfAKeyIsMet(i2, c2, k, vc)
// {
//     var m1 := FoldMetaSet2(c1[k], i1[k]);
//     var m2 := FoldMetaSet2(c2[k], i2[k]);
//     assume VCEq(m1.vc, m2.vc) || VCHappendsBefore(m1.vc, m2.vc);
// }

lemma lemma_AVersionIsMetOnAllServersWillAlwaysMet(
    b:Behavior<CMState>,
    i:int,
    k:Key,
    vc:VectorClock
)
    requires 1 < i
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires CMNext(b[i-2], b[i-1])
    requires k in Keys_domain
    requires VectorClockValid(vc)
    requires AVersionIsMetOnAllServers(b, i-1, k, vc)
    requires ServerNextDoesNotDecreaseVersions(b[i-1], b[i])
    ensures AVersionIsMetOnAllServers(b, i, k, vc)
{
    assert forall j :: 0 <= j < |b[i-1].servers| ==> 
        CCacheDoesNotDecrease(b[i-1].servers[j].s.ccache, b[i].servers[j].s.ccache) 
        && ICacheDoesNotDecrease(b[i-1].servers[j].s.icache, b[i].servers[j].s.icache);
    
    forall j | 0 <= j < |b[i].servers| 
        ensures AVersionOfAKeyIsMet(b[i].servers[j].s.icache, b[i].servers[j].s.ccache, k, vc)
    {
        assert AVersionOfAKeyIsMet(b[i-1].servers[j].s.icache, b[i-1].servers[j].s.ccache, k, vc);
        assert CCacheDoesNotDecrease(b[i-1].servers[j].s.ccache, b[i].servers[j].s.ccache);
        assert ICacheDoesNotDecrease(b[i-1].servers[j].s.icache, b[i].servers[j].s.icache);
        assert ServerValid(b[i-1].servers[j].s);
        assert ServerValid(b[i].servers[j].s);
        lemma_AVersionIsMetWillAlwaysMet(
            b[i-1].servers[j].s.icache,
            b[i].servers[j].s.icache,
            b[i-1].servers[j].s.ccache,
            b[i].servers[j].s.ccache,
            k,
            vc
        );
        assert AVersionOfAKeyIsMet(b[i].servers[j].s.icache, b[i].servers[j].s.ccache, k, vc);
    }
}

lemma lemma_AllVersionsInDepsAreMetOnAllServersWillAlwaysMet(
    b:Behavior<CMState>,
    i:int,
    deps:Dependency
)
    requires 1 < i
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    // requires CMNext(b[i-2], b[i-1])
    requires DependencyValid(deps)
    requires ServerNextDoesNotDecreaseVersions(b[i-1], b[i])
    requires AllVersionsInDepsAreMetOnAllServers(b, i-1, deps)
    ensures AllVersionsInDepsAreMetOnAllServers(b, i, deps)
{
    lemma_BehaviorValidImpliesOneStepValid(b, i-1);
    reveal_AllVersionsInDepsAreMetOnAllServers();
    assert forall j :: 0 <= j < |b[i-1].servers| ==> 
        CCacheDoesNotDecrease(b[i-1].servers[j].s.ccache, b[i].servers[j].s.ccache) 
        && ICacheDoesNotDecrease(b[i-1].servers[j].s.icache, b[i].servers[j].s.icache);
    
    forall k | k in deps 
        ensures AVersionIsMetOnAllServers(b, i, k, deps[k])
    {
        assert AVersionIsMetOnAllServers(b, i-1, k, deps[k]);
        lemma_AVersionIsMetOnAllServersWillAlwaysMet(b, i, k, deps[k]);
        assert AVersionIsMetOnAllServers(b, i, k, deps[k]);
    }
}

// lemma {:axiom} lemma_AllDepsInICacheAreMetOnAllServersWillAlwaysMet(
//     b:Behavior<CMState>,
//     i:int,
//     idx:int
// )
//     requires 1 < i
//     requires IsValidBehaviorPrefix(b, i)
//     requires CMNext(b[i-1], b[i])
//     // requires CMNext(b[i-2], b[i-1])
//     requires 0 <= idx < Nodes
//     requires ServerNextDoesNotDecreaseVersions(b[i-1], b[i])
//     requires AllDepsInICacheAreMetOnAllServers(b, i-1, b[i].servers[idx].s.icache)
//     ensures AllDepsInICacheAreMetOnAllServers(b, i, b[i].servers[idx].s.icache)
// {
//     assert forall j :: 0 <= j < |b[i-1].servers| ==> 
//         CCacheDoesNotDecrease(b[i-1].servers[j].s.ccache, b[i].servers[j].s.ccache) 
//         && ICacheDoesNotDecrease(b[i-1].servers[j].s.icache, b[i].servers[j].s.icache);
    
//     var icache := b[i].servers[idx].s.icache;
//     assert ICacheValid(icache);
//     assert AllDepsInICacheAreMetOnAllServers(b, i-1, icache);

//     forall k | k in icache
//     {
//         forall m:Meta | m in icache[k] 
//         {
//             forall kk | kk in m.deps 
//                 ensures AVersionIsMetOnAllServers(b, i, kk, m.deps[kk])
//             {
//                 assert AVersionIsMetOnAllServers(b, i-1, kk, m.deps[kk]);
//                 lemma_AVersionIsMetOnAllServersWillAlwaysMet(b, i, kk, m.deps[kk]);
//                 assert AVersionIsMetOnAllServers(b, i, kk, m.deps[kk]);
//             }
//         }
//     }

//     assert forall k :: k in icache ==>
//             forall m:Meta :: m in icache[k] ==> 
//                 forall kk :: kk in m.deps ==> AVersionIsMetOnAllServers(b, i, kk, m.deps[kk]);
// }

lemma lemma_AllVersionsInCCacheAreMetOnAllServersWillAlwaysMet(
    b:Behavior<CMState>,
    i:int,
    idx:int
)
    requires 1 < i
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    // requires CMNext(b[i-2], b[i-1])
    requires 0 <= idx < Nodes
    requires ServerNextDoesNotDecreaseVersions(b[i-1], b[i])
    requires AllVersionsInCCacheAreMetOnAllServers(b, i-1, b[i].servers[idx].s.ccache)
    ensures AllVersionsInCCacheAreMetOnAllServers(b, i, b[i].servers[idx].s.ccache)
{
    assert i-1 > 0;
    assert IsValidBehaviorPrefix(b, i-1);
    lemma_BehaviorValidImpliesOneStepValid(b, i-1);
    reveal_AllVersionsInCCacheAreMetOnAllServers();
    assert forall j :: 0 <= j < |b[i-1].servers| ==> 
        CCacheDoesNotDecrease(b[i-1].servers[j].s.ccache, b[i].servers[j].s.ccache) 
        && ICacheDoesNotDecrease(b[i-1].servers[j].s.icache, b[i].servers[j].s.icache);

    var ccache := b[i].servers[idx].s.ccache;

    forall k | k in ccache
        ensures AVersionIsMetOnAllServers(b, i, k, ccache[k].vc)
        ensures AllVersionsInDepsAreMetOnAllServers(b, i, ccache[k].deps)
    {
        assert AVersionIsMetOnAllServers(b, i-1, k, ccache[k].vc);
        lemma_AVersionIsMetOnAllServersWillAlwaysMet(b, i, k, ccache[k].vc);
        lemma_AllVersionsInDepsAreMetOnAllServersWillAlwaysMet(b, i, ccache[k].deps);
    }
}

}