include "../distributed_system.dfy"
include "packet_sending.dfy"
include "properties.dfy"
include "environment.dfy"
include "deps_are_met.dfy"
include "read_reply_is_met.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module CausalMesh_Proof_ServersAreMet_i {
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
import opened CausalMesh_Proof_Environment_i
import opened CausalMesh_Proof_DepsAreMet_i
import opened CausalMesh_Proof_ReadReplyIsMet_i
import opened Collections__Seqs_s
import opened Collections__Maps_i
import opened Collections__Maps2_s

lemma lemma_ServersAreMetForCMNext(b:Behavior<CMState>, i:int, idx:int)
    requires IsValidBehaviorPrefix(b, i+1)
    requires 0 < i
    requires 0 <= idx < |b[i].servers|
    requires 0 <= idx < |b[i+1].servers|
    requires b[i].servers[idx] != b[i+1].servers[idx]
    requires CMNext(b[i], b[i+1])
    requires AllServersAreMet(b, i)
    requires AllVersionsInCCacheAreMetOnAllServers(b, i, b[i].servers[idx].s.ccache)
    // requires AllVersionsInDepsAreMetOnAllServers(b, i-1, p.msg.deps_read)
    requires AllDepsInICacheAreMetOnAllServers(b, i, b[i].servers[idx].s.icache)
    requires AllReadDepsAreMet(b, i)
    requires ServerNextDoesNotDecreaseVersions(b[i], b[i+1])
    // ensures AllServersAreMet(b, i+1)
{
    var s := b[i].servers[idx].s;
    var s' := b[i+1].servers[idx].s;

    var ios := lemma_ActionThatChangesServerIsThatServersAction(b, i, idx);
    assert CMNextServer(b[i], b[i+1], idx, ios);
    assert LServerNext(b[i].servers[idx], b[i+1].servers[idx], ios);
    assert ServerValid(s);

    assert ios[0].LIoOpReceive?;
    var p := ios[0].r;
    var sp := ExtractSentPacketsFromIos(ios);
    assert p.msg.Message_Read? || p.msg.Message_Write? || p.msg.Message_Propagation?;
    assert p in b[i].environment.sentPackets;

    // lemma_BehaviorValidImpliesOneStepValid(b, i-1);

    assert ServerProcessPacket(s, s', ios);
    if p.msg.Message_Read? {
        assert ReceiveRead(s, s', p, sp);
        var (new_icache, new_ccache) := PullDeps2(s.icache, s.ccache, p.msg.deps_read);
        assert AllReadDepsAreMet(b, i);
        assert forall pp :: pp in b[i].environment.sentPackets && pp.msg.Message_Read? ==> 
            AllVersionsInDepsAreMetOnAllServers(b, i, pp.msg.deps_read);
        assert AllVersionsInDepsAreMetOnAllServers(b, i, p.msg.deps_read);
        lemma_VersionsAfterPullDepsAreMetOnAllServers(b, i, idx, p.msg.deps_read);
        
        assert AllVersionsInCCacheAreMetOnAllServers(b, i, new_ccache);

        lemma_CCacheIsMetOnAllServersWillAlwaysMet(b, i+1, new_ccache);
        lemma_ICacheIsMetOnAllServersWillAlwaysMet(b, i+1, new_icache);
        assert s'.icache == new_icache;
        assert s'.ccache == new_ccache;
        assert AllVersionsInCCacheAreMetOnAllServers(b, i+1, b[i+1].servers[idx].s.ccache);
        assert AllDepsInICacheAreMetOnAllServers(b, i+1, b[i+1].servers[idx].s.icache);
    } 
    else if p.msg.Message_Write?
    {
        assert ReceiveWrite(s, s', p, sp);
        assert s'.icache == s.icache;
        assert s'.ccache == s.ccache;
        lemma_CCacheIsMetOnAllServersWillAlwaysMet(b, i+1, s.ccache);
        assert AllVersionsInCCacheAreMetOnAllServers(b, i+1, b[i+1].servers[idx].s.ccache);
    }
}


lemma lemma_CCacheIsMetOnAllServersWillAlwaysMet(
    b:Behavior<CMState>,
    i:int,
    ccache:CCache
)
    requires 1 < i
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires CCacheValid(ccache)
    requires ServerNextDoesNotDecreaseVersions(b[i-1], b[i])
    requires AllVersionsInCCacheAreMetOnAllServers(b, i-1, ccache)
    ensures AllVersionsInCCacheAreMetOnAllServers(b, i, ccache)
{
    assert i-1 > 0;
    assert IsValidBehaviorPrefix(b, i-1);
    lemma_BehaviorValidImpliesOneStepValid(b, i-1);
    reveal_AllVersionsInCCacheAreMetOnAllServers();

    forall k | k in ccache
        ensures AVersionIsMetOnAllServers(b, i, k, ccache[k].vc)
        ensures AllVersionsInDepsAreMetOnAllServers(b, i, ccache[k].deps)
    {
        assert AVersionIsMetOnAllServers(b, i-1, k, ccache[k].vc);
        lemma_AVersionIsMetOnAllServersWillAlwaysMet(b, i, k, ccache[k].vc);
        lemma_AllVersionsInDepsAreMetOnAllServersWillAlwaysMet(b, i, ccache[k].deps);
    }
}

lemma lemma_ICacheIsMetOnAllServersWillAlwaysMet(
    b:Behavior<CMState>,
    i:int,
    icache:ICache
)
    requires 1 < i
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires ICacheValid(icache)
    requires ServerNextDoesNotDecreaseVersions(b[i-1], b[i])
    requires AllDepsInICacheAreMetOnAllServers(b, i-1, icache)
    ensures AllDepsInICacheAreMetOnAllServers(b, i, icache)
{
    assert i-1 > 0;
    assert IsValidBehaviorPrefix(b, i-1);
    lemma_BehaviorValidImpliesOneStepValid(b, i-1);
    reveal_AllDepsInICacheAreMetOnAllServers();

    forall k | k in icache
    {
        forall m:Meta | m in icache[k] 
        {
            forall kk | kk in m.deps 
                ensures AVersionIsMetOnAllServers(b, i, kk, m.deps[kk])
            {
                assert AVersionIsMetOnAllServers(b, i-1, kk, m.deps[kk]);
                lemma_AVersionIsMetOnAllServersWillAlwaysMet(b, i, kk, m.deps[kk]);
                assert AVersionIsMetOnAllServers(b, i, kk, m.deps[kk]);
            }
        }
    }

    assert forall k :: k in icache ==>
            forall m:Meta :: m in icache[k] ==> 
                forall kk :: kk in m.deps ==> AVersionIsMetOnAllServers(b, i, kk, m.deps[kk]);
}
}