include "../distributed_system.dfy"
// include "causalcut.dfy"
include "packet_sending.dfy"
include "properties.dfy"
include "environment.dfy"
// include "deps_are_met.dfy"
// include "monotonic_read.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module CausalMesh_Proof_CacheDoesNotDecrease_i {
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
import opened CausalMesh_Proof_Environment_i
import opened Collections__Seqs_s
import opened Collections__Maps_i
import opened Collections__Maps2_s

lemma lemma_CMNextCacheDoesNotDecreasePrefix(
    b:Behavior<CMState>,
    i:int
)
    requires 0 <= i 
    requires IsValidBehaviorPrefix(b, i+1)
    requires forall j :: 0 <= j <= i ==> CMNext(b[j], b[j+1])
    // requires AllServersAreCausalCut(b[0])
    ensures forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
    decreases i
{
    if i == 0 {
        return;
    }

    lemma_ConstantsAllConsistent(b, i-1);
    lemma_ConstantsAllConsistent(b, i);

    lemma_BehaviorValidImpliesOneStepValid(b, i);
    assert CMNext(b[i-1], b[i]);

    lemma_CMNextCacheDoesNotDecreasePrefix(b, i-1);
    assert forall j :: 0 <= j < i - 1 ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1]);
    lemma_CMNextCacheDoesNotDecrease(b, i-1);
    assert ServerNextDoesNotDecreaseVersions(b[i-1], b[i]);
    lemma_CMNextCacheDoesNotDecreasePrefix_helper(b, i);
    assert forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1]);
}

lemma lemma_CMNextCacheDoesNotDecreasePrefix_helper(
    b:Behavior<CMState>,
    i:int
)
    requires 0 <= i 
    requires IsValidBehaviorPrefix(b, i)
    requires forall j :: 0 <= j <= i ==> CMNext(b[j], b[j+1])
    requires CMNext(b[i-1], b[i])
    requires forall j :: 0 <= j < i - 1 ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
    requires ServerNextDoesNotDecreaseVersions(b[i-1], b[i])
    ensures forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
    decreases i
{

}

lemma lemma_CMNextCacheDoesNotDecrease(b:Behavior<CMState>, i:int)
    requires IsValidBehaviorPrefix(b, i+1)
    requires 0 <= i
    // requires forall j :: 0 <= j <= i ==> CMNext(b[j], b[j+1])
    requires CMNext(b[i], b[i+1])
    // requires ServerNextDoesNotDecreaseVersions(b[i-1], b[i])
    ensures ServerNextDoesNotDecreaseVersions(b[i], b[i+1])
{
    var ps := b[i];
    var ps' := b[i+1];

    if ps.servers == ps'.servers {
        assert ServerNextDoesNotDecreaseVersions(b[i], b[i+1]);
    } 
    else {
        var idx :| 0 <= idx < |ps.servers| && ps.servers[idx] != ps'.servers[idx];
        lemma_CMNextCacheDoesNotDecrease_helper(b, i, idx);
    }
}

lemma lemma_CMNextCacheDoesNotDecrease_helper(b:Behavior<CMState>, i:int, idx:int)
    requires IsValidBehaviorPrefix(b, i+1)
    requires 0 <= i
    requires 0 <= idx < |b[i].servers|
    requires 0 <= idx < |b[i+1].servers|
    requires b[i].servers[idx] != b[i+1].servers[idx]
    // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    requires CMNext(b[i], b[i+1])
    // requires ServerNextDoesNotDecreaseVersions(b[i-1], b[i])
    ensures ServerNextDoesNotDecreaseVersions(b[i], b[i+1])
{
    var s := b[i].servers[idx].s;
    var s' := b[i+1].servers[idx].s;

    assert IsValidBehaviorPrefix(b, i+1);
    assert 0 <= i;
    assert 0 <= idx < |b[i].servers|;
    assert 0 <= idx < |b[i+1].servers|;
    assert b[i+1].servers[idx] != b[i].servers[idx];
    var ios := lemma_ActionThatChangesServerIsThatServersAction(b, i, idx);
    assert CMNextServer(b[i], b[i+1], idx, ios);
    assert LServerNext(b[i].servers[idx], b[i+1].servers[idx], ios);
    assert ServerValid(s);

    assert ios[0].LIoOpReceive?;
    var p := ios[0].r;
    var sp := ExtractSentPacketsFromIos(ios);
    assert p.msg.Message_Read? || p.msg.Message_Write? || p.msg.Message_Propagation?;

    assert ServerProcessPacket(s, s', ios);

    if p.msg.Message_Read? {
        assert ReceiveRead(s, s', p, sp);
        var (new_icache, new_ccache) := PullDeps2(s.icache, s.ccache, p.msg.deps_read);
        lemma_PullDeps2DoneNotDecreaseVersions(s.icache, s.ccache, p.msg.deps_read);
        assert s'.icache == new_icache;
        assert s'.ccache == new_ccache;
        assert CCacheDoesNotDecrease(s.ccache, s'.ccache);
        assert ICacheDoesNotDecrease(s.icache, s'.icache);
    } 
    else if p.msg.Message_Write?
    {
        assert ReceiveWrite(s, s', p, sp);
        assert CCacheDoesNotDecrease(s.ccache, s'.ccache);
        assert ICacheDoesNotDecrease(s.icache, s'.icache);
    }
    else {
        assert p.msg.Message_Propagation?;
        assert ReceivePropagate(s, s', p, sp);
        if s.next == p.msg.start {
            var (new_icache, new_ccache) := PullDeps2(s.icache, s.ccache, p.msg.meta.deps);
            lemma_PullDeps2DoneNotDecreaseVersions(s.icache, s.ccache, p.msg.meta.deps);
            assert s'.icache == new_icache;
            assert CCacheDoesNotDecrease(s.ccache, new_ccache);
            var merged_meta := MetaMerge(new_ccache[p.msg.key], p.msg.meta);
            var new_ccache' := InsertIntoCCache(new_ccache, merged_meta);
            assert CCacheDoesNotDecrease(new_ccache, new_ccache');
            // assert VCHappendsBefore(new_ccache[p.msg.key].vc, )
            // assert s'.ccache == new_ccache;
            assert CCacheDoesNotDecrease(s.ccache, s'.ccache);
            assert ICacheDoesNotDecrease(s.icache, s'.icache);
        }
    }
    assert CCacheDoesNotDecrease(s.ccache, s'.ccache);
    assert ICacheDoesNotDecrease(s.icache, s'.icache);
    assert forall j :: 0 <= j < |b[i].servers| && j != idx ==> 
            b[i].servers[j].s.ccache == b[i+1].servers[j].s.ccache && b[i].servers[j].s.icache == b[i+1].servers[j].s.icache;
    assert forall j :: 0 <= j < |b[i].servers| && j != idx ==>
            CCacheDoesNotDecrease(b[i].servers[j].s.ccache, b[i+1].servers[j].s.ccache) 
            && ICacheDoesNotDecrease(b[i].servers[j].s.icache, b[i+1].servers[j].s.icache);
    lemma_CMNextCacheDoesNotDecrease_helper2(b, i, idx);
    assert ServerNextDoesNotDecreaseVersions(b[i], b[i+1]);
}

lemma lemma_CMNextCacheDoesNotDecrease_helper2(b:Behavior<CMState>, i:int, idx:int)
    requires IsValidBehaviorPrefix(b, i)
    requires 0 <= i
    requires 0 <= idx < |b[i].servers|
    requires 0 <= idx < |b[i+1].servers|
    requires b[i].servers[idx] != b[i+1].servers[idx]
    // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    requires CMNext(b[i], b[i+1])
    requires forall j :: 0 <= j < |b[i].servers| && j != idx ==>
            CCacheDoesNotDecrease(b[i].servers[j].s.ccache, b[i+1].servers[j].s.ccache) 
            && ICacheDoesNotDecrease(b[i].servers[j].s.icache, b[i+1].servers[j].s.icache)
    requires CCacheDoesNotDecrease(b[i].servers[idx].s.ccache, b[i+1].servers[idx].s.ccache)
    requires ICacheDoesNotDecrease(b[i].servers[idx].s.icache, b[i+1].servers[idx].s.icache)
    ensures ServerNextDoesNotDecreaseVersions(b[i], b[i+1])
{

}

lemma lemma_PullDeps2DoneNotDecreaseVersions(
    icache:ICache, ccache:CCache, deps:Dependency
)
    requires ICacheValid(icache)
    requires CCacheValid(ccache)
    requires CausalCut(ccache)
    requires forall k :: k in Keys_domain ==> k in icache && k in ccache
    requires forall k :: k in ccache ==> k in icache
    requires DependencyValid(deps)
    requires forall k :: k in deps ==> k in icache
    ensures var (new_icache, new_ccache) := PullDeps2(icache, ccache, deps);
        CCacheDoesNotDecrease(ccache, new_ccache) && ICacheDoesNotDecrease(icache, new_icache)
{
    var domain := icache.Keys + deps.Keys;
    var todos := GetMetasOfAllDeps(icache, deps, map[], domain);
    var new_cache := MergeCCache(ccache, todos);
    assert CCacheDoesNotDecrease(ccache, new_cache);

    var (new_icache, new_ccache) := PullDeps2(icache, ccache, deps);
    assert ICacheDoesNotDecrease(icache, new_icache);

    assert new_ccache == new_cache;
}

}