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
        |vc| == Nodes
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
        && forall i :: 0 <= i < |vc1| && vc1[i] <= vc2[i]
    }

    function VCMerge(vc1:VectorClock, vc2:VectorClock) : (res:VectorClock)
        requires VectorClockValid(vc1)
        requires VectorClockValid(vc2)
        ensures VectorClockValid(res)
    {
        MergeSeqs(vc1, vc2)
    }

    function MergeSeqs(s1:seq<int>, s2:seq<int>) : (res:seq<int>)
        requires |s1| == |s2|
        ensures |res| == |s1|
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

    function DependencyMerge(dep1:Dependency, dep2:Dependency) : Dependency
        requires DependencyValid(dep1)
        requires DependencyValid(dep2)
    {
        map k | k in dep1.Keys + dep2.Keys ::
            if k in dep1 && k in dep2 then
                VCMerge(dep1[k], dep2[k])
            else if k in dep1 then
                dep1[k]
            else
                dep2[k]
    }

    function DependencyInsertOrMerge(dep:Dependency, k:Key, vc:VectorClock) : (res:Dependency)
        requires DependencyValid(dep)
        requires k in Keys_domain
        requires VectorClockValid(vc)
        ensures DependencyValid(res)
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
    {
        m1.(vc := VCMerge(m1.vc, m2.vc), deps := DependencyMerge(m1.deps, m2.deps))
    }

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
        ensures ICacheValid(res)
    {
        if m.key in c then
            c[m.key := c[m.key] + {m}]
        else
            c[m.key := {m}]
    }


}