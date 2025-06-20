module CausalMesh_Types_i {

    const Nodes:nat := 3

    const Clients:nat := 5

    const MaxKeys:nat := 10000

    const Keys_domain:set<int> := set i | 0 <= i <= 10000 :: i;

    type Key = int

    type Val = int

    type VectorClock = seq<int>

    predicate VectorClockValid(vc:VectorClock)
    {
        && |vc| == Nodes
        && forall i :: 0 <= i < |vc| ==> vc[i] >= 0
    }

    function EmptyVC() : (res:VectorClock)
        ensures VectorClockValid(res)
    {
        seq(Nodes, (idx) => 0)
    }

    function VCEq(vc1:VectorClock, vc2:VectorClock) : bool 
        requires VectorClockValid(vc1)
        requires VectorClockValid(vc2)
    {
        forall i :: 0 <= i < |vc1| ==> vc1[i] == vc2[i]
    }

    function VCHappendsBefore(vc1:VectorClock, vc2:VectorClock) : bool 
        requires VectorClockValid(vc1)
        requires VectorClockValid(vc2)
    {
        && !VCEq(vc1, vc2)
        && forall i :: 0 <= i < |vc1| ==> vc1[i] <= vc2[i]
    }

    lemma lemma_VCRelationIsTransitive(vc:VectorClock, vc1:VectorClock, vc2:VectorClock)
        requires VectorClockValid(vc)
        requires VectorClockValid(vc2)
        requires VectorClockValid(vc1)
        requires VCHappendsBefore(vc, vc1) || VCEq(vc, vc1)
        requires VCHappendsBefore(vc1, vc2) || VCEq(vc1, vc2)
        ensures VCHappendsBefore(vc, vc2) || VCEq(vc, vc2)
    {

    }

    lemma lemma_VCMergePreserveTheRelation(vc1:VectorClock, vc2:VectorClock, vc:VectorClock)
        requires VectorClockValid(vc)
        requires VectorClockValid(vc2)
        requires VectorClockValid(vc1)
        requires VCHappendsBefore(vc1, vc) || VCEq(vc1, vc)
        requires VCHappendsBefore(vc2, vc) || VCEq(vc2, vc)
        ensures VCHappendsBefore(VCMerge(vc1, vc2), vc) || VCEq(VCMerge(vc1, vc2), vc)
    {

    }

    function VCMerge(vc1:VectorClock, vc2:VectorClock) : (res:VectorClock)
        requires VectorClockValid(vc1)
        requires VectorClockValid(vc2)
        ensures VectorClockValid(res)
        ensures (VCHappendsBefore(vc1, res) || VCEq(vc1, res))
        ensures (VCHappendsBefore(vc2, res) || VCEq(vc2, res))
    {
        MergeSeqs(vc1, vc2)
    }

    function MergeSeqs(s1:seq<int>, s2:seq<int>) : (res:seq<int>)
        requires |s1| == |s2|
        ensures |res| == |s1|
        ensures forall i :: 0 <= i < |s1| ==> s1[i] <= res[i] && s2[i] <= res[i]
        ensures forall i :: 0 <= i < |s1| ==> res[i] == s1[i] || res[i] == s2[i]
    {   
        if |s1| == 0 then
            []
        else if s1[0] > s2[0] then
            [s1[0]] + MergeSeqs(s1[1..], s2[1..])
        else
            [s2[0]] + MergeSeqs(s1[1..], s2[1..])
    }

    type Dependency = map<Key, VectorClock>

    predicate DependencyValid(dep:Dependency)
    {
        forall k :: k in dep ==> k in Keys_domain && VectorClockValid(dep[k])
    }

    function DependencyEq(dep1:Dependency, dep2:Dependency) : bool 
        requires DependencyValid(dep1)
        requires DependencyValid(dep2)
    {
        forall k :: k in dep1 ==> k in dep2 && VCEq(dep1[k], dep2[k])
    }

    function DependencyMerge(dep1:Dependency, dep2:Dependency) : (res:Dependency)
        requires DependencyValid(dep1)
        requires DependencyValid(dep2)
        ensures DependencyValid(res)
        ensures forall k :: k in dep1 ==> k in res 
        ensures forall k :: k in dep2 ==> k in res
        ensures res.Keys == dep1.Keys + dep2.Keys
    {
        map k | k in dep1.Keys + dep2.Keys ::
            if k in dep1 && k in dep2 then
                VCMerge(dep1[k], dep2[k])
            else if k in dep1 then
                dep1[k]
            else
                dep2[k]
    }

    lemma lemma_DependencyMergeDominatedByTheLargerOne(dep1:Dependency, dep2:Dependency)
        requires DependencyValid(dep1)
        requires DependencyValid(dep2)
        requires forall k :: k in dep1 ==>
                        k in dep2 &&
                        (VCHappendsBefore(dep1[k], dep2[k]) || VCEq(dep1[k], dep2[k]))
        ensures DependencyMerge(dep1, dep2) == dep2
    {
        assert forall k :: k in DependencyMerge(dep1, dep2) <==> k in dep2;
        
        assert forall k :: k in dep2 ==> DependencyMerge(dep1, dep2)[k] == dep2[k];
    }

    function DependencyInsertOrMerge(dep:Dependency, k:Key, vc:VectorClock) : (res:Dependency)
        requires DependencyValid(dep)
        requires k in Keys_domain
        requires VectorClockValid(vc)
        ensures DependencyValid(res)
        ensures k in res
    {
        if k in dep then
            var d := dep[k := VCMerge(dep[k], vc)];
            assert DependencyValid(d);
            d
        else 
            dep[k := vc]
    }


    datatype Meta = Meta (
        key : Key,
        // val : Val,
        vc : VectorClock,
        deps : Dependency
    )

    predicate MetaValid(m:Meta) 
    {
        && m.key in Keys_domain
        && VectorClockValid(m.vc)
        && DependencyValid(m.deps)
        && forall k :: k in m.deps ==> VCHappendsBefore(m.deps[k], m.vc) || VCEq(m.deps[k], m.vc)
    }

    predicate MetaEq(m1:Meta, m2:Meta)
        requires MetaValid(m1)
        requires MetaValid(m2)
    {
        && m1.key == m2.key
        && VCEq(m1.vc, m2.vc)
        && DependencyEq(m1.deps, m2.deps)
    }

    predicate MetaHappensBefore(m1:Meta, m2:Meta)
        requires MetaValid(m1)
        requires MetaValid(m2)
    {
        VCHappendsBefore(m1.vc, m2.vc)
    }

    function MetaMerge(m1:Meta, m2:Meta) : (res:Meta)
        requires m1.key == m2.key
        requires MetaValid(m1)
        requires MetaValid(m2)
        ensures MetaValid(res)
    {
        m1.(vc := VCMerge(m1.vc, m2.vc), deps := DependencyMerge(m1.deps, m2.deps))
    }

    function FoldMetaSet(acc: Meta, metas: set<Meta>, domain:set<Key>) : (res:Meta)
        requires MetaValid(acc)
        requires forall kk :: kk in acc.deps ==> kk in domain
        requires forall m :: m in metas ==> MetaValid(m) && m.key == acc.key && (forall kk :: kk in m.deps ==> kk in domain)
        ensures MetaValid(res)
        ensures res.key == acc.key
        // ensures VCHappendsBefore(acc.vc, res.vc) || VCEq(acc.vc, res.vc)
        // ensures forall m :: m in metas ==> 
        //         VCHappendsBefore(m.vc, res.vc) || VCEq(m.vc, res.vc);
        ensures forall kk :: kk in res.deps ==> kk in domain && (VCHappendsBefore(res.deps[kk], res.vc) || VCEq(res.deps[kk], res.vc))
        decreases |metas|
    {
        if |metas| == 0 then
            acc
        else
            var x :| x in metas;
            FoldMetaSet(MetaMerge(acc, x), metas - {x}, domain)
    }

    function FoldMetaSet2(acc: Meta, metas: set<Meta>) : (res:Meta)
        requires MetaValid(acc)
        // requires forall kk :: kk in acc.deps ==> kk in domain
        requires forall m :: m in metas ==> MetaValid(m) && m.key == acc.key // && (forall kk :: kk in m.deps ==> kk in domain)
        ensures MetaValid(res)
        ensures res.key == acc.key
        ensures VCHappendsBefore(acc.vc, res.vc) || VCEq(acc.vc, res.vc)
        ensures forall m :: m in metas ==> 
                VCHappendsBefore(m.vc, res.vc) || VCEq(m.vc, res.vc);
        ensures forall kk :: kk in res.deps ==> 
                //kk in domain 
                && (VCHappendsBefore(res.deps[kk], res.vc) || VCEq(res.deps[kk], res.vc))
        decreases |metas|
    {
        if |metas| == 0 then
            acc
        else
            var x :| x in metas;
            FoldMetaSet2(MetaMerge(acc, x), metas - {x})
    }

    // lemma VCMergeBounded(metas: set<Meta>, bound: VectorClock)
    //     requires forall m :: m in metas ==> VCHappendsBefore(m.vc, bound) || VCEq(m.vc, bound)
    //     ensures VCHappendsBefore(FoldMetaSet(metas).vc, bound) || VCEq(FoldMetaSet(metas).vc, bound)
    // {
    //     // inductive proof over FoldVC
    // }

    lemma lemma_FoldMetaBounded(acc: Meta, metas: set<Meta>, bound: VectorClock, domain: set<Key>)
        requires MetaValid(acc)
        requires VectorClockValid(bound)
        requires forall kk :: kk in acc.deps ==> kk in domain
        requires forall m :: m in metas ==> MetaValid(m) && m.key == acc.key && (forall kk :: kk in m.deps ==> kk in domain)
        requires VCHappendsBefore(acc.vc, bound) || VCEq(acc.vc, bound)
        requires forall m :: m in metas ==> VCHappendsBefore(m.vc, bound) || VCEq(m.vc, bound)
        ensures  VCHappendsBefore(FoldMetaSet(acc, metas, domain).vc, bound) || VCEq(FoldMetaSet(acc, metas, domain).vc, bound)
        decreases |metas|
    {
        if |metas| == 0 {
            return;
        }

        var x :| x in metas;

        // Step 1: prove MetaMerge(acc, x).vc <= bound
        assert VCHappendsBefore(acc.vc, bound) || VCEq(acc.vc, bound);
        assert VCHappendsBefore(x.vc, bound) || VCEq(x.vc, bound);
        assert VCHappendsBefore(MetaMerge(acc, x).vc, bound) || VCEq(MetaMerge(acc, x).vc, bound);

        // Step 2: call induction on smaller set
        lemma_FoldMetaBounded(MetaMerge(acc, x), metas - {x}, bound, domain);
    }


    function FoldVC(acc: VectorClock, vcs: set<VectorClock>) : (res:VectorClock)
        requires VectorClockValid(acc)
        requires forall m :: m in vcs ==> VectorClockValid(m)
        ensures VectorClockValid(res)
        ensures forall vc :: vc in vcs ==> VCHappendsBefore(vc, res) || VCEq(vc, res)
        ensures VCHappendsBefore(acc, res) || VCEq(acc, res)
        decreases |vcs|
    {
        if |vcs| == 0 then
            acc
        else
            var x :| x in vcs;
            var merged := VCMerge(acc, x);
            assert VCHappendsBefore(x, merged) || VCEq(x, merged);
            var res := FoldVC(VCMerge(acc, x), vcs - {x});
            res
    }

    function FoldDependency(acc: Dependency, deps: set<Dependency>) : (res:Dependency)
        requires DependencyValid(acc)
        requires forall m :: m in deps ==> DependencyValid(m)
        ensures DependencyValid(res)
        decreases |deps|
    {
        if |deps| == 0 then
            acc
        else
            var x :| x in deps;
            FoldDependency(DependencyMerge(acc, x), deps - {x})
    }

    function FoldDependencyFromMetaSet(acc: Dependency, metas: set<Meta>) : (res:Dependency)
        requires DependencyValid(acc)
        requires forall m :: m in metas ==> MetaValid(m)
        ensures DependencyValid(res)
        decreases |metas|
    {
        if |metas| == 0 then
            acc
        else
            var x :| x in metas;
            FoldDependencyFromMetaSet(DependencyMerge(acc, x.deps), metas - {x})
    }

    lemma {:axiom} lemma_FoldDependencyFromMetaSet(
        deps:Dependency,
        metas:set<Meta>,
        vc:VectorClock
    )
        requires DependencyValid(deps)
        requires forall m :: m in metas ==> MetaValid(m)
        requires VectorClockValid(vc)
        requires forall m :: m in metas ==> VCHappendsBefore(m.vc, vc) || VCEq(m.vc, vc)
        requires forall k :: k in deps ==> VCHappendsBefore(deps[k], vc) || VCEq(deps[k], vc)
        ensures var res := FoldDependencyFromMetaSet(deps, metas);
                forall k :: k in res ==> VCHappendsBefore(res[k], vc) || VCEq(res[k], vc)
    
    // lemma lemma_FoldDependencyFromMetaSet2(
    //     acc: Dependency,
    //     metas: set<Meta>,
    //     vc: VectorClock
    // )
    //     requires DependencyValid(acc)
    //     requires forall m :: m in metas ==> MetaValid(m)
    //     requires VectorClockValid(vc)
    //     requires forall m :: m in metas ==> VCHappendsBefore(m.vc, vc) || VCEq(m.vc, vc)
    //     requires forall k :: k in acc ==> VCHappendsBefore(acc[k], vc) || VCEq(acc[k], vc)
    //     ensures var res := FoldDependencyFromMetaSet(acc, metas);
    //             forall k :: k in res ==> VCHappendsBefore(res[k], vc) || VCEq(res[k], vc)
    // {
    //     if |metas| == 0 {
    //         // res == acc
    //         assert FoldDependencyFromMetaSet(acc, metas) == acc;
    //         assert forall k :: k in acc ==> VCHappendsBefore(acc[k], vc) || VCEq(acc[k], vc);
    //     } else {
    //         var x :| x in metas;
    //         var m := x;
    //         var acc2 := DependencyMerge(acc, m.deps);
    //         lemma_FoldDependencyFromMetaSet2(acc2, metas - {x}, vc);

    //         // goal: forall k in FoldDependencyFromMetaSet(acc2, metas - {x}) ==> ... ⪯ vc

    //         // subgoal: for all k in acc2, acc2[k] ⪯ vc
    //         assert forall k :: k in acc2
    //             ==> VCHappendsBefore(acc2[k], vc) || VCEq(acc2[k], vc)
    //             by {
    //                 forall k | k in acc2 {
    //                     if k in acc && k in m.deps {
    //                         // acc[k] ⪯ vc, m.deps[k] ⪯ vc
    //                         assert VCHappendsBefore(acc[k], vc) || VCEq(acc[k], vc);
    //                         assert VCHappendsBefore(m.deps[k], vc) || VCEq(m.deps[k], vc);
    //                         // VCMerge preserves upper bound
    //                         assert VCHappendsBefore(VCMerge(acc[k], m.deps[k]), vc)
    //                             || VCEq(VCMerge(acc[k], m.deps[k]), vc)
    //                             by {
    //                                 lemma_VCRelationIsTransitive(acc[k], VCMerge(acc[k], m.deps[k]), vc);
    //                             }
    //                     } else if k in acc {
    //                         assert VCHappendsBefore(acc[k], vc) || VCEq(acc[k], vc);
    //                         assert acc2[k] == acc[k];
    //                     } else {
    //                         assert k in m.deps;
    //                         assert VCHappendsBefore(m.deps[k], vc) || VCEq(m.deps[k], vc);
    //                         assert acc2[k] == m.deps[k];
    //                     }
    //                 }
    //             }

    //         // 然后递归地调用证明
    //         lemma_FoldDependencyFromMetaSet2(acc2, metas - {x}, vc);
    //     }
    // }


    lemma {:axiom} lemma_MapRemoveSubsetOfTheValOfKey<K,V>(m:map<K,set<V>>, k:K, s:set<V>)
        requires k in m && m[k] >= s
        ensures |m.Values| > |m[k := m[k] - s].Values|
    

    function EmptyMeta(k:Key) : (res:Meta)
        requires k in Keys_domain
        ensures MetaValid(res)
    {
        Meta(k, seq(Nodes, (idx) => 0), map[])
    }

    type CCache = map<Key, Meta>

    predicate CCacheValid(c:CCache)
    {
        forall k :: k in c ==> k in Keys_domain && MetaValid(c[k]) && c[k].key == k
    }

    function InsertIntoCCache(c:CCache, m:Meta) : (res:CCache)
        requires CCacheValid(c)
        requires MetaValid(m)
        ensures CCacheValid(res)
        ensures m.key in res
        ensures VCHappendsBefore(m.vc, res[m.key].vc) || VCEq(m.vc, res[m.key].vc)
    {
        if m.key in c then
            c[m.key := MetaMerge(c[m.key], m)]
        else 
            c[m.key := m]
    }

    function MergeCCache(c1:CCache, c2:CCache) : (res:CCache)
        requires CCacheValid(c1)
        requires CCacheValid(c2)
        ensures CCacheValid(res)
    {
        map k | k in c1.Keys + c2.Keys ::
            if k in c1 && k in c2 then
                MetaMerge(c1[k], c2[k])
            else if k in c1 then
                c1[k]
            else
                c2[k]
    }

    type ICache = map<Key, set<Meta>>

    predicate ICacheValid(c:ICache)
    {
        forall k :: k in c ==> k in Keys_domain && (forall m :: m in c[k] ==> MetaValid(m) && m.key == k 
            && (forall kk :: kk in m.deps ==> kk in c))
    }

    function AddMetaToICache(c:ICache, m:Meta) : (res:ICache)
        requires ICacheValid(c)
        requires MetaValid(m)
        requires forall k :: k in m.deps ==> k in c
        ensures m.key in res
        ensures m in res[m.key]
        ensures forall k :: k in c ==> k in res && forall m :: m in c[k] ==> m in res[k]
        ensures ICacheValid(res)
    {
        if m.key in c then
            c[m.key := c[m.key] + {m}]
        else
            c[m.key := {m}]
    }

    function AddMetasToICache(c:ICache, metas:set<Meta>) : (res:ICache)
        requires ICacheValid(c)
        requires forall m :: m in metas ==> MetaValid(m) && forall k :: k in m.deps ==> k in c
        ensures ICacheValid(res)
        // ensures forall m :: m in metas ==> m.key in res && m in res[m.key]
        decreases |metas|
    {
        if |metas| == 0 then 
            c
        else 
            var m :| m in metas;
            var new_metas := metas - {m};
            AddMetasToICache(AddMetaToICache(c, m), new_metas)
    }

    lemma {:axiom} lemma_AddMetasToICache_ensures_contains(
        c: ICache,
        metas: set<Meta>
    )
        requires ICacheValid(c)
        requires forall m :: m in metas ==> MetaValid(m) && forall k :: k in m.deps ==> k in c
        ensures forall m :: m in metas ==> m.key in AddMetasToICache(c, metas) && m in AddMetasToICache(c, metas)[m.key]
        ensures forall k :: k in c ==> k in AddMetasToICache(c, metas) && forall m :: m in c[k] ==> m in AddMetasToICache(c, metas)[k]
        // ensures ICacheValid(AddMetasToICache(c, metas))
        decreases |metas|
    // {
    //     if |metas| == 0 {
    //         assert AddMetasToICache(c, metas) == c;
    //     } else {
    //         var m :| m in metas;
    //         var c2 := AddMetaToICache(c, m);

    //         assert m.key in c2 && m in c2[m.key];

    //         assert ICacheValid(c2);

    //         lemma_AddMetasToICache_ensures_contains(c2, metas - {m});

    //         assert forall m0 :: m0 in metas ==> 
    //             m0 in AddMetasToICache(c, metas)[m0.key];
    //     }
    // }

    predicate NodesAreNext(i:int, j:int)
        requires 0 <= i < Nodes
        requires 0 <= j < Nodes
    {
        if i == Nodes - 1 then
            j == 0 
        else 
            j == i + 1
    }
}