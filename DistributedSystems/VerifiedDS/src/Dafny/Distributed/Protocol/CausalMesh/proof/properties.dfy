include "../distributed_system.dfy"
include "../../../Common/Logic/Temporal/Rules.i.dfy"
include "constants.dfy"

module CausalMesh_Proof_Properties_i {
import opened CausalMesh_Cache_i
import opened CausalMesh_Message_i
import opened CausalMesh_Types_i
import opened Environment_s
import opened CausalMesh_DistributedSystem_i
import opened CausalMesh_Properties_i
import opened Temporal__Temporal_s
import opened Collections__Maps2_s
import opened CausalMesh_Proof_Constants_i
import opened CausalMesh_proof_Assumptions_i

predicate AVersionIsMetOnAllServers(
    b:Behavior<CMState>,
    i:int,
    k:Key,
    vc:VectorClock
)
    requires 0 < i
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    requires k in Keys_domain
    requires VectorClockValid(vc)
{
    // assert CMNextCommon(b[i-1], b[i]);
    assert (forall j {:trigger CMNext(b[j], b[j+1])} :: 0 <= j < i ==> CMNext(b[j], b[j+1]));
    assert CMNext(b[i-1], b[i]);
    forall j :: 0 <= j < |b[i].servers| ==> AVersionOfAKeyIsMet(b[i].servers[j].s.icache, b[i].servers[j].s.ccache, k, vc)
}

predicate AllVersionsInDepsAreMetOnAllServers(
    b:Behavior<CMState>,
    i:int,
    deps:Dependency
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    requires CMNext(b[i-1], b[i])
    requires DependencyValid(deps)
{
    forall k :: k in deps ==> AVersionIsMetOnAllServers(b, i, k, deps[k])
}

predicate AllVersionsInCCacheAreMetOnAllServers(
    b:Behavior<CMState>,
    i:int,
    ccache:CCache
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    requires CCacheValid(ccache)
{
    && (forall k :: k in ccache ==> AVersionIsMetOnAllServers(b, i, k, ccache[k].vc))
    && (forall k :: k in ccache ==> AllVersionsInDepsAreMetOnAllServers(b, i, ccache[k].deps))
}

predicate AllDepsInCCacheAreMetOnAllServers(
    b:Behavior<CMState>,
    i:int,
    ccache:CCache
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    requires CCacheValid(ccache)
{
    forall k :: k in ccache ==>
        forall kk :: kk in ccache[k].deps ==> AVersionIsMetOnAllServers(b, i, kk, ccache[k].deps[kk])
}

predicate AllDepsInICacheAreMetOnAllServers(
    b:Behavior<CMState>,
    i:int,
    icache:ICache
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    // requires forall j {:trigger CMNext(b[j], b[j+1])} :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    // requires ICacheValid(icache)
    requires forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> MetaValid(m) && m.key == k
                && (forall kk :: kk in m.deps ==> kk in Keys_domain))
{
    forall k :: k in icache ==>
        forall m :: m in icache[k] ==> 
            forall kk :: kk in m.deps ==> AVersionIsMetOnAllServers(b, i, kk, m.deps[kk])
}
}