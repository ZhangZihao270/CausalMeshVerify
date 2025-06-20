include "../distributed_system.dfy"
// include "causalcut.dfy"
include "packet_sending.dfy"
include "properties.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module CausalMesh_Proof_DepsAreMet_i {
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
import opened Collections__Seqs_s
import opened Collections__Maps_i
import opened Collections__Maps2_s

lemma lemma_MergedVCIsMetOnAllServers(
    b:Behavior<CMState>,
    i:int,
    k:Key,
    vc1:VectorClock,
    vc2:VectorClock
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires VectorClockValid(vc1)
    requires VectorClockValid(vc2)
    requires k in Keys_domain
    requires AVersionIsMetOnAllServers(b, i, k, vc1)
    requires AVersionIsMetOnAllServers(b, i, k, vc2)
    ensures AVersionIsMetOnAllServers(b, i, k, VCMerge(vc1, vc2))
{

}

lemma lemma_MergedDepsIsMetOnAllServers(
    b:Behavior<CMState>,
    i:int,
    dep1:Dependency,
    dep2:Dependency
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires DependencyValid(dep1)
    requires DependencyValid(dep2)
    requires AllVersionsInDepsAreMetOnAllServers(b, i, dep1)
    requires AllVersionsInDepsAreMetOnAllServers(b, i, dep2)
    ensures AllVersionsInDepsAreMetOnAllServers(b, i, DependencyMerge(dep1, dep2))
{
    reveal_AllVersionsInDepsAreMetOnAllServers();
    var merged := DependencyMerge(dep1, dep2);
    if |dep1.Keys + dep2.Keys| == 0 {
        assert merged == map[];
        assert AllVersionsInDepsAreMetOnAllServers(b, i, merged);
        return;
    }

    var k :| k in dep1.Keys + dep2.Keys;

    if k in dep1 && k !in dep2 {
        assert merged[k] == dep1[k];
        assert AVersionIsMetOnAllServers(b, i, k, merged[k]);
    } else if k in dep2 && k !in dep1 {
        assert AVersionIsMetOnAllServers(b, i, k, merged[k]);
    } else {
        assert merged[k] == VCMerge(dep1[k], dep2[k]);
        lemma_MergedVCIsMetOnAllServers(b, i, k, dep1[k], dep2[k]);
        assert AVersionIsMetOnAllServers(b, i, k, merged[k]);
    }
}

lemma lemma_MergeCCacheEnsuresAllVersionAreMetOnAllServers(
    b: Behavior<CMState>,
    i: int,
    ccache: CCache,
    metas: map<Key, Meta>
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires CCacheValid(ccache)
    requires CCacheValid(metas)
    requires AllVersionsInCCacheAreMetOnAllServers(b, i, ccache)
    requires AllVersionsInCCacheAreMetOnAllServers(b, i, metas)
    ensures AllVersionsInCCacheAreMetOnAllServers(b, i, MergeCCache(ccache, metas))
{
    reveal_AllVersionsInCCacheAreMetOnAllServers();
    var merged := MergeCCache(ccache, metas);
    forall k | k in merged
        ensures AVersionIsMetOnAllServers(b, i, k, merged[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, merged[k].deps)
    {
        if k in ccache && k !in metas {
            assert merged[k] == ccache[k];
        } else if k !in ccache && k in metas {
            assert merged[k] == metas[k];
        } else {
            assert merged[k] == MetaMerge(ccache[k], metas[k]);
            lemma_MergedVCIsMetOnAllServers(b, i, k, ccache[k].vc, metas[k].vc);
            lemma_MergedDepsIsMetOnAllServers(b, i, ccache[k].deps, metas[k].deps);
        }
    }
} 

// lemma lemma_MergeCCacheEnsuresAllVersionAreMetOnAllServers(
//     b:Behavior<CMState>,
//     i:int,
//     ccache:CCache,
//     metas:map<Key, Meta>
// )
//     requires i > 0
//     requires IsValidBehaviorPrefix(b, i)
//     requires CMNext(b[i-1], b[i])
//     requires CCacheValid(ccache)
//     requires CCacheValid(metas)
//     requires AllVersionsInCCacheAreMetOnAllServers(b, i, ccache)
//     requires AllVersionsInCCacheAreMetOnAllServers(b, i, metas)
//     // ensures AllVersionsInCCacheAreMetOnAllServers(b, i, MergeCCache(ccache, metas))
// {
//     var merged := MergeCCache(ccache, metas);
//     if |ccache.Keys + metas.Keys| == 0 {
//         assert merged == map[];
//         assert AllVersionsInCCacheAreMetOnAllServers(b, i, merged);
//         return;
//     }

//     // var k :| k in ccache.Keys + metas.Keys;
//     // if k in ccache && k !in metas {
//     //     assert merged[k] == ccache[k];
//     //     assert AVersionIsMetOnAllServers(b, i, k, merged[k].vc);
//     //     assert AllVersionsInDepsAreMetOnAllServers(b, i, merged[k].deps);
//     // } else if k !in ccache && k in metas {
//     //     assert AVersionIsMetOnAllServers(b, i, k, merged[k].vc);
//     //     assert AllVersionsInDepsAreMetOnAllServers(b, i, merged[k].deps);
//     // } else {
//     //     assert merged[k] == MetaMerge(ccache[k], metas[k]);
//     //     lemma_MergedVCIsMetOnAllServers(b, i, k, ccache[k].vc, metas[k].vc);
//     //     // assert AVersionIsMetOnAllServers(b, i, k, VCMerge(ccache[k].vc, metas[k].vc));
//     //     assert AVersionIsMetOnAllServers(b, i, k, merged[k].vc);
//     //     lemma_MergedDepsIsMetOnAllServers(b, i, ccache[k].deps, metas[k].deps);
//     //     assert AllVersionsInDepsAreMetOnAllServers(b, i, merged[k].deps);
//     // }
//     assert ccache.Keys + metas.Keys == merged.Keys;
//     assert forall k :: k in merged.Keys ==>
//     (if k in ccache && k !in metas then
//         merged[k] == ccache[k] &&
//         AVersionIsMetOnAllServers(b, i, k, merged[k].vc) &&
//         AllVersionsInDepsAreMetOnAllServers(b, i, merged[k].deps)
//      else if k in metas && k !in ccache then
//         merged[k] == metas[k] &&
//         AVersionIsMetOnAllServers(b, i, k, merged[k].vc) &&
//         AllVersionsInDepsAreMetOnAllServers(b, i, merged[k].deps)
//      else // both in
//         lemma_MergedVCIsMetOnAllServers(b, i, k, ccache[k].vc, metas[k].vc);
//         lemma_MergedDepsIsMetOnAllServers(b, i, ccache[k].deps, metas[k].deps);
//         merged[k] == MetaMerge(ccache[k], metas[k]) 
//         &&
//         AVersionIsMetOnAllServers(b, i, k, merged[k].vc) &&
//         AllVersionsInDepsAreMetOnAllServers(b, i, merged[k].deps)
//     );

//     // assert forall k :: k in merged ==> AVersionIsMetOnAllServers(b, i, k, merged[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, merged[k].deps);
// }

// lemma lemma_VersionsAfterPullDepsAreMetOnAllServers(
//     b:Behavior<CMState>,
//     i:int,
//     idx:int,
//     deps:Dependency
// )
//     requires i > 0
//     requires IsValidBehaviorPrefix(b, i)
//     requires CMNext(b[i], b[i+1])
//     requires 0 <= idx < Nodes
//     requires DependencyValid(deps)
//     requires AllDepsInICacheAreMetOnAllServers(b, i, b[i].servers[idx].s.icache)
//     requires AllVersionsInDepsAreMetOnAllServers(b, i, deps)
//     requires AllVersionsInCCacheAreMetOnAllServers(b, i, b[i].servers[idx].s.ccache)
//     ensures var res := PullDeps2(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, deps);
//             AllVersionsInCCacheAreMetOnAllServers(b, i, res.1)
// {
//     lemma_BehaviorValidImpliesOneStepValid(b, i);
//     reveal_AllVersionsInDepsAreMetOnAllServers();
//     reveal_AllDepsInICacheAreMetOnAllServers();
//     reveal_AllVersionsInCCacheAreMetOnAllServers();
    
//     // assert CMNextCommon(b[i-1], b[i]);
//     var icache := b[i].servers[idx].s.icache;
//     var ccache := b[i].servers[idx].s.ccache;
//     var domain := icache.Keys + deps.Keys;

//     var todos := GetMetasOfAllDeps(icache, deps, map[], domain);
//     var todos1 := GetMetasOfAllDepsGlobalView(b, i, idx, icache, deps, map[], domain);
//     assert forall k :: k in todos1 ==> AVersionIsMetOnAllServers(b, i, k, todos1[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos1[k].deps);
//     lemma_GetMetasOfAllDepsGlobalViewEqualsToGetMetasOfAllDeps(b, i, idx, icache, deps, map[], domain);
//     assert todos == todos1;
//     assert forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps);

//     var new_cache := MergeCCache(ccache, todos);
//     lemma_MergeCCacheEnsuresAllVersionAreMetOnAllServers(b, i, ccache, todos);
//     assert AllVersionsInCCacheAreMetOnAllServers(b, i, new_cache);

//     var res := PullDeps2(icache, ccache, deps);
//     assert res.1 == new_cache;
//     assert AllVersionsInCCacheAreMetOnAllServers(b, i, res.1);
//     // assert AllVersionsInCCacheAreMetOnAllServers(b, i, new_cache);
//     // assume AllVersionsInDepsAreMetOnAllServers(b, i, deps);
//     // assume AllVersionsInCCacheAreMetOnAllServers(b, i, ccache);
// }

lemma {:axiom} lemma_AllMeatsAreMetImpliesMergedMetaIsMet(
    b:Behavior<CMState>,
    i:int,
    initial:Meta, metas:set<Meta>, domain:set<Key> 
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires MetaValid(initial)
    requires forall kk :: kk in initial.deps ==> kk in domain
    requires forall m :: m in metas ==> MetaValid(m) && m.key == initial.key && (forall kk :: kk in m.deps ==> kk in domain)
    requires forall kk :: kk in initial.deps ==> AVersionIsMetOnAllServers(b, i, kk, initial.deps[kk])
    requires forall m :: m in metas ==> forall kk :: kk in m.deps ==> AVersionIsMetOnAllServers(b, i, kk, m.deps[kk])
    ensures var merged := FoldMetaSet(initial, metas, domain);
            forall kk :: kk in merged.deps ==> AVersionIsMetOnAllServers(b, i, kk, merged.deps[kk])
// {
    
// }

lemma {:axiom} lemma_MetaMapIsMetImpliesInsertedMataMapIsMet(
    b:Behavior<CMState>,
    i:int,
    todos:map<Key, Meta>,
    m:Meta
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires forall k :: k in todos ==> MetaValid(todos[k]) && todos[k].key == k 
                    && forall kk :: kk in todos[k].deps ==> 
                        VCHappendsBefore(todos[k].deps[kk], todos[k].vc) || VCEq(todos[k].deps[kk], todos[k].vc)
    requires MetaValid(m)
    requires forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps)
    requires AVersionIsMetOnAllServers(b, i, m.key, m.vc) && AllVersionsInDepsAreMetOnAllServers(b, i, m.deps)
    ensures var res := AddMetaToMetaMap(todos, m);
            forall k :: k in res ==> AVersionIsMetOnAllServers(b, i, k, res[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, res[k].deps)
// {

// }

// function GetMetasOfAllDepsGlobalView(
//     b:Behavior<CMState>,
//     i:int,
//     idx:int,
//     icache:ICache,
//     deps:Dependency,
//     todos:map<Key, Meta>,
//     domain:set<Key>
// ) : (res:map<Key, Meta>)
//     requires i > 0
//     requires IsValidBehaviorPrefix(b, i)
//     requires CMNext(b[i-1], b[i])
//     requires forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> MetaValid(m) && m.key == k
//                 && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))
//     requires DependencyValid(deps)
//     requires forall k :: k in todos ==> MetaValid(todos[k]) && todos[k].key == k 
//     requires forall k :: k in Keys_domain ==> k in icache // should we have this?
//     requires forall k :: k in deps ==> k in domain 

//     requires AllDepsInICacheAreMetOnAllServers(b, i, icache)
//     requires AllVersionsInDepsAreMetOnAllServers(b, i, deps)
//     requires forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps)

//     ensures forall k :: k in res ==> MetaValid(res[k]) && res[k].key == k 
//     ensures forall k :: k in res ==> AVersionIsMetOnAllServers(b, i, k, res[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, res[k].deps)
//     decreases |icache.Values|, |deps|
// {
//     // lemma_BehaviorValidImpliesOneStepValid(b, i);
//     reveal_AllVersionsInDepsAreMetOnAllServers();
//     reveal_AllDepsInICacheAreMetOnAllServers();
//     reveal_AllVersionsInCCacheAreMetOnAllServers();
    
//     assert forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps);
//     if |deps| == 0 then 
//         todos
//     else 
//         var k :| k in deps;
//         var new_deps := RemoveElt(deps, k);
//         if k in todos && (VCHappendsBefore(deps[k], todos[k].vc) || VCEq(deps[k], todos[k].vc)) then 
//             var res := GetMetasOfAllDepsGlobalView(b, i, idx, icache, new_deps, todos, domain);
//             res
//         else 
//             var metas := set m | m in icache[k] && (VCHappendsBefore(m.vc, deps[k]) || VCEq(m.vc, deps[k]));
//             if |metas| > 0 then 
//                 var initial := EmptyMeta(k);
//                 var merged := FoldMetaSet(initial, metas, domain);
//                 var meta := merged.(vc := deps[k]);
                
                
//                 lemma_FoldMetaBounded(initial, metas, deps[k], domain);
//                 assert (VCHappendsBefore(merged.vc, meta.vc) || VCEq(merged.vc, meta.vc));

//                 var new_cache := icache[k:= icache[k] - metas];
//                 assert icache[k] >= metas;
//                 lemma_MapRemoveSubsetOfTheValOfKey(icache, k, metas);
//                 assert |new_cache.Values| < |icache.Values|;

//                 assert AllDepsInICacheAreMetOnAllServers(b, i, new_cache);
//                 lemma_AllMeatsAreMetImpliesMergedMetaIsMet(b, i, initial, metas, domain);
//                 assert AllVersionsInDepsAreMetOnAllServers(b, i, merged.deps);

//                 var res := GetMetasOfAllDepsGlobalView(b, i, idx, new_cache, merged.deps, todos, domain);

//                 assert forall k :: k in res ==> AVersionIsMetOnAllServers(b, i, k, res[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, res[k].deps);
//                 assert AVersionIsMetOnAllServers(b, i, k, meta.vc);

//                 var todos' := AddMetaToMetaMap(res, meta);

//                 assert AllVersionsInDepsAreMetOnAllServers(b, i, new_deps);
//                 lemma_MetaMapIsMetImpliesInsertedMataMapIsMet(b, i, res, meta);
//                 assert forall k :: k in todos' ==> AVersionIsMetOnAllServers(b, i, k, todos'[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos'[k].deps);

//                 var res' := GetMetasOfAllDepsGlobalView(b, i, idx, icache, new_deps, todos', domain);
//                 res'
//             else 
//                 var initial := EmptyMeta(k);
//                 var meta := initial.(vc:=deps[k]);
                
//                 var todos' := AddMetaToMetaMap(todos, meta);
                
//                 var res := GetMetasOfAllDepsGlobalView(b, i, idx, icache, new_deps, todos', domain);
//                 res
// }

// function GetMetasOfAllDepsGlobalView(
//     b:Behavior<CMState>,
//     i:int,
//     idx:int,
//     icache:ICache,
//     deps:Dependency,
//     todos:map<Key, Meta>,
//     domain:set<Key>
// ) : (res:map<Key, Meta>)
//     requires i > 0
//     requires IsValidBehaviorPrefix(b, i)
//     requires CMNext(b[i-1], b[i])
//     requires forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> MetaValid(m) && m.key == k
//                 && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))
//     requires DependencyValid(deps)
//     requires forall k :: k in todos ==> MetaValid(todos[k]) && todos[k].key == k 
//     requires forall k :: k in Keys_domain ==> k in icache // should we have this?
//     requires forall k :: k in deps ==> k in domain 

//     requires AllDepsInICacheAreMetOnAllServers(b, i, icache)
//     requires AllVersionsInDepsAreMetOnAllServers(b, i, deps)
//     requires forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps)

//     ensures forall k :: k in res ==> MetaValid(res[k]) && res[k].key == k 
//     ensures forall k :: k in res ==> AVersionIsMetOnAllServers(b, i, k, res[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, res[k].deps)
//     decreases |icache.Values|, |deps|
// {
//     // lemma_BehaviorValidImpliesOneStepValid(b, i);
//     reveal_AllVersionsInDepsAreMetOnAllServers();
//     reveal_AllDepsInICacheAreMetOnAllServers();
//     reveal_AllVersionsInCCacheAreMetOnAllServers();
    
//     assert forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps);
//     if |deps| == 0 then 
//         todos
//     else 
//         var k :| k in deps;
//         var new_deps := RemoveElt(deps, k);
//         if k in todos && (VCHappendsBefore(deps[k], todos[k].vc) || VCEq(deps[k], todos[k].vc)) then 
//             var res := GetMetasOfAllDepsGlobalView(b, i, idx, icache, new_deps, todos, domain);
//             res
//         else 
//             var metas := set m | m in icache[k] && (VCHappendsBefore(m.vc, deps[k]) || VCEq(m.vc, deps[k]));
//             if |metas| > 0 then 
//                 var initial := EmptyMeta(k);
//                 var merged := FoldMetaSet(initial, metas, domain);
//                 var meta := merged.(vc := deps[k]);
                
                
//                 lemma_FoldMetaBounded(initial, metas, deps[k], domain);
//                 assert (VCHappendsBefore(merged.vc, meta.vc) || VCEq(merged.vc, meta.vc));

//                 var new_cache := icache[k:= icache[k] - metas];
//                 assert icache[k] >= metas;
//                 lemma_MapRemoveSubsetOfTheValOfKey(icache, k, metas);
//                 assert |new_cache.Values| < |icache.Values|;

//                 assert AllDepsInICacheAreMetOnAllServers(b, i, new_cache);
//                 lemma_AllMeatsAreMetImpliesMergedMetaIsMet(b, i, initial, metas, domain);
//                 assert AllVersionsInDepsAreMetOnAllServers(b, i, merged.deps);

//                 var res := GetMetasOfAllDepsGlobalView(b, i, idx, new_cache, merged.deps, todos, domain);

//                 assert forall k :: k in res ==> AVersionIsMetOnAllServers(b, i, k, res[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, res[k].deps);
//                 assert AVersionIsMetOnAllServers(b, i, k, meta.vc);

//                 var todos' := AddMetaToMetaMap(res, meta);

//                 assert AllVersionsInDepsAreMetOnAllServers(b, i, new_deps);
//                 lemma_MetaMapIsMetImpliesInsertedMataMapIsMet(b, i, res, meta);
//                 assert forall k :: k in todos' ==> AVersionIsMetOnAllServers(b, i, k, todos'[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos'[k].deps);

//                 var res' := GetMetasOfAllDepsGlobalView(b, i, idx, icache, new_deps, todos', domain);
//                 res'
//             else 
//                 var initial := EmptyMeta(k);
//                 var meta := initial.(vc:=deps[k]);
                
//                 var todos' := AddMetaToMetaMap(todos, meta);
                
//                 var res := GetMetasOfAllDepsGlobalView(b, i, idx, icache, new_deps, todos', domain);
//                 res
// }

// lemma {:axiom} lemma_TwoMetaMapAreEqual(m1:map<Key, Meta>, m2:map<Key, Meta>)
//     ensures m1 == m2

// lemma {:axiom} lemma_GetMetasOfAllDepsGlobalViewEqualsToGetMetasOfAllDeps
// (
//     b:Behavior<CMState>,
//     i:int,
//     idx:int,
//     icache:ICache,
//     deps:Dependency,
//     todos:map<Key, Meta>,
//     domain:set<Key>
// )
//     requires i > 0
//     requires IsValidBehaviorPrefix(b, i)
//     requires CMNext(b[i-1], b[i]);
//     requires forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> MetaValid(m) && m.key == k
//                 && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))
//     requires DependencyValid(deps)
//     requires forall k :: k in todos ==> MetaValid(todos[k]) && todos[k].key == k 
//     requires forall k :: k in Keys_domain ==> k in icache // should we have this?
//     requires forall k :: k in deps ==> k in domain 

//     requires forall k :: k in todos ==> forall kk :: kk in todos[k].deps ==> 
//                         VCHappendsBefore(todos[k].deps[kk], todos[k].vc) || VCEq(todos[k].deps[kk], todos[k].vc)
//     requires CausalCut(todos)

//     requires AllDepsInICacheAreMetOnAllServers(b, i, icache)
//     requires AllVersionsInDepsAreMetOnAllServers(b, i, deps)
//     requires forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps)
//     ensures 
//             var res1 := GetMetasOfAllDepsGlobalView(b, i, idx, icache, deps, todos, domain);
//             var res2 := GetMetasOfAllDeps(icache, deps, todos, domain);
//             res1 == res2
}