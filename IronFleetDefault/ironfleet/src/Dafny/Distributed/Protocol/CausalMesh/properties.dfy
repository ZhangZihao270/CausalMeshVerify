include "../../Common/Collections/Maps.i.dfy"
include "types.dfy"
include "message.dfy"

module CausalMesh_Properties_i {
    import opened Collections__Maps_i
    import opened CausalMesh_Types_i
    import opened CausalMesh_Message_i
    
    /** Key Properties */

    predicate CausalCut(ccache: CCache)
        // requires CCacheValid(ccache)
        requires forall k :: k in ccache ==> MetaValid(ccache[k])
    {
        forall k :: k in ccache ==>
            forall kk :: kk in ccache[k].deps ==>
                kk in ccache &&
                (VCHappendsBefore(ccache[k].deps[kk], ccache[kk].vc) || VCEq(ccache[k].deps[kk], ccache[kk].vc))
    }

    predicate ReadsDepsAreMet2(icache:ICache, ccache:CCache, deps:Dependency)
        requires ICacheValid(icache)
        requires CCacheValid(ccache)
        requires forall k :: k in Keys_domain ==> k in icache && k in ccache
        requires DependencyValid(deps)
    {
        forall k :: k in deps ==> 
            var m := FoldMetaSet(ccache[k], icache[k], icache.Keys);
            VCEq(deps[k], m.vc) || VCHappendsBefore(deps[k], m.vc)
    }

    predicate ReadsDepsAreMet(icache:ICache, ccache:CCache, deps:Dependency)
        requires ICacheValid(icache)
        requires CCacheValid(ccache)
        requires forall k :: k in Keys_domain ==> k in icache && k in ccache
        requires DependencyValid(deps)
    {
        forall k :: k in deps ==> 
            (VCEq(deps[k], ccache[k].vc) || VCHappendsBefore(deps[k], ccache[k].vc))
            || exists m :: m in icache[k] && m.vc == deps[k]
            // var m := FoldMetaSet(ccache[k], icache[k], icache.Keys);
            // VCEq(deps[k], m.vc) || VCHappendsBefore(deps[k], m.vc)
    }

    predicate UponReadsDepsAreMet(ccache:CCache, deps:Dependency)
        requires CCacheValid(ccache)
        requires forall k :: k in Keys_domain ==> k in ccache
        requires DependencyValid(deps)
    {
        forall k :: k in deps ==> 
            VCEq(deps[k], ccache[k].vc) || VCHappendsBefore(deps[k], ccache[k].vc)
    }
    
    lemma lemma_MergeCCacheRemainsCausalCut(c1:CCache, c2:CCache)
        requires CCacheValid(c1)
        requires CCacheValid(c2)
        requires CausalCut(c1)
        requires CausalCut(c2)
        ensures CCacheValid(MergeCCache(c1,c2))
        ensures CausalCut(MergeCCache(c1,c2))
    {
        // map k | k in c1.Keys + c2.Keys ::
        //     if k in c1 && k in c2 then
        //         MetaMerge(c1[k], c2[k])
        //     else if k in c1 then
        //         c1[k]
        //     else
        //         c2[k]
    }
}