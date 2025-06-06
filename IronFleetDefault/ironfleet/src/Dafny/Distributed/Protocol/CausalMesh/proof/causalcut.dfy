include "../distributed_system.dfy"
include "action.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module CausalMesh_Proof_CausalCut_i {
import opened CausalMesh_Cache_i
import opened CausalMesh_Message_i
import opened CausalMesh_Types_i
import opened Environment_s
import opened CausalMesh_DistributedSystem_i
import opened CausalMesh_Proof_Actions_i
import opened Temporal__Temporal_s
import opened CausalMesh_proof_Assumptions_i
import opened CausalMesh_Proof_Constants_i
import opened Collections__Seqs_s
// import opened Collections__Sets_i
import opened Collections__Maps2_s

function {:opaque} ConvertBehaviorSeqToImap<T>(s:seq<T>):imap<int, T>
  requires |s| > 0
  ensures  imaptotal(ConvertBehaviorSeqToImap(s))
  ensures  forall i :: 0 <= i < |s| ==> ConvertBehaviorSeqToImap(s)[i] == s[i]
{
  imap i {:trigger s[i]} :: if i < 0 then s[0] else if 0 <= i < |s| then s[i] else last(s)
}

lemma lemma_AllServersAreCausalSet(
    low_level_behavior:seq<CMState>
)
    requires |low_level_behavior| > 0 
    requires CMInit(low_level_behavior[0])
    requires forall i {:trigger CMNext(low_level_behavior[i], low_level_behavior[i+1])} :: 
                0 <= i < |low_level_behavior| - 1 ==> CMNext(low_level_behavior[i], low_level_behavior[i+1])
    ensures forall i :: 0 <= i < |low_level_behavior| ==> AllServersAreCausalCut(low_level_behavior[i])
{
    assert AllServersAreCausalCut(low_level_behavior[0]);

    var b := ConvertBehaviorSeqToImap(low_level_behavior);
    lemma_AllServersAreCausalSetPrefix(b, |low_level_behavior|-1);
}

lemma lemma_AllServersAreCausalSetPrefix(
    b:Behavior<CMState>,
    i:int
)
    requires 0 <= i 
    requires IsValidBehaviorPrefix(b, i)
    requires AllServersAreCausalCut(b[0])
    ensures forall j :: 0 <= j <= i ==> AllServersAreCausalCut(b[j])
{
    if i == 0 {
        return;
    }

    lemma_ConstantsAllConsistent(b, i-1);
    lemma_ConstantsAllConsistent(b, i);

    lemma_AllServersAreCausalSetPrefix(b, i-1);
    assert forall j :: 0 <= j < i ==> AllServersAreCausalCut(b[j]);

    lemma_CMNextRemainsCausalCut(b, i-1);
    assert AllServersAreCausalCut(b[i]);
}

// lemma lemma_CMNextRemainsCausalCut(low_level_behavior:seq<CMState>, i:int)
//     requires |low_level_behavior| > 1
//     requires 0 <= i < |low_level_behavior| - 1
//     requires CMNext(low_level_behavior[i], low_level_behavior[i+1])
//     requires AllServersAreCausalCut(low_level_behavior[i])
//     // ensures AllServersAreCausalCut(low_level_behavior[i+1])
// {
//     var ps := low_level_behavior[i];
//     var ps' := low_level_behavior[i+1];

//     if ps.servers == ps'.servers {
//         assert AllServersAreCausalCut(ps');
//     } 
//     // else {
//     //     assume AllServersAreCausalCut(ps');
//     // }
// }

lemma lemma_CMNextRemainsCausalCut(b:Behavior<CMState>, i:int)
    requires IsValidBehaviorPrefix(b, i+1)
    requires 0 <= i
    // requires 0 <= i < |low_level_behavior| - 1
    requires CMNext(b[i], b[i+1])
    requires AllServersAreCausalCut(b[i])
    ensures AllServersAreCausalCut(b[i+1])
{
    var ps := b[i];
    var ps' := b[i+1];

    if ps.servers == ps'.servers {
        assert AllServersAreCausalCut(ps');
    } 
    else {
        var idx :| 0 <= idx < |ps.servers| && ps.servers[idx] != ps'.servers[idx];
        lemma_CMNextServerRemainsCausalCut(b, i, idx);
    }
}

lemma lemma_CMNextServerRemainsCausalCut(b:Behavior<CMState>, i:int, idx:int)
    requires IsValidBehaviorPrefix(b, i+1)
    requires 0 <= i
    requires 0 <= idx < |b[i].servers|
    requires 0 <= idx < |b[i+1].servers|
    requires b[i].servers[idx] != b[i+1].servers[idx]
    requires AllServersAreCausalCut(b[i])
    ensures AllServersAreCausalCut(b[i+1])
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

    assert ServerProcessPacket(s, s', ios);

    if p.msg.Message_Read? {
        assert ReceiveRead(s, s', p, sp);
        lemma_PullDeps2RemainsCausalCut(s.icache, s.ccache, p.msg.deps_read);
        assert CausalCut(s'.ccache);
    } 
    else 
    if p.msg.Message_Write? {
        assert ReceiveWrite(s, s', p, sp);
        assert CausalCut(s'.ccache);
    } 
    else {
        assert p.msg.Message_Propagation?;
        assert ReceivePropagate(s, s', p, sp);
        if s.next == p.msg.start {
            var deps := set x | x in p.msg.metas :: x.deps;
            var new_deps := FoldDependency(map[], deps);
            lemma_PullDeps2RemainsCausalCut(s.icache, s.ccache, new_deps);
        }
        
        assert CausalCut(s'.ccache);
    }
 
}

lemma {:axiom} lemma_PullDeps2RemainsCausalCut(icache:ICache, ccache:CCache, deps:Dependency)
    requires ICacheValid(icache)
    requires CCacheValid(ccache)
    requires forall k :: k in ccache ==> k in icache
    requires DependencyValid(deps)
    requires forall k :: k in deps ==> k in icache
    requires CausalCut(ccache)
    ensures var (new_icache, new_ccache) := PullDeps2(icache, ccache, deps);
            CausalCut(new_ccache)

}