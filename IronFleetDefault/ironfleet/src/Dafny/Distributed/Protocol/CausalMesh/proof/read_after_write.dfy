include "../distributed_system.dfy"
include "causalcut.dfy"
include "packet_sending.dfy"
include "message_read_reply.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module CausalMesh_Proof_Read_After_Write_i {
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
import opened CausalMesh_Proof_CausalCut_i
import opened CausalMesh_Proof_PacketSending_i
import opened CausalMesh_Proof_MessageReadReply_i
import opened Collections__Seqs_s
import opened Collections__Maps_i
import opened Collections__Maps2_s

// lemma lemma_AllDepsInCCacheAfterPullDepsAreExistsInICache()

predicate WriteReplyIsLargerThanVCInDeps(deps:Dependency, vc:VectorClock)
    requires DependencyValid(deps)
    requires VectorClockValid(vc)
{
    forall k :: k in deps ==> VCHappendsBefore(deps[k], vc) || VCEq(deps[k], vc)
}

predicate WriteReplyIsLargerThanVCInLocal(local:map<Key, Meta>, vc:VectorClock)
    requires forall k :: k in local ==> MetaValid(local[k])
    requires VectorClockValid(vc)
{
    forall k :: k in local ==> VCHappendsBefore(local[k].vc, vc) || VCEq(local[k].vc, vc)
}

predicate WriteReplyHasCorrspondingWriteWithSmallerVC(
    b:Behavior<CMState>,
    i:int,
    p:Packet
)
    requires 0 < i 
    requires IsValidBehaviorPrefix(b, i)
    requires p in b[i].environment.sentPackets && p.msg.Message_Write_Reply? && PacketValid(p)
{
    lemma_BehaviorValidImpliesOneStepValid(b, i);
    forall wp :: wp in b[i].environment.sentPackets && wp.msg.Message_Write?
                    && p.msg.key_wreply == wp.msg.key_write
                    && p.dst == wp.src
                    ==> WriteReplyIsLargerThanVCInDeps(wp.msg.deps_write, p.msg.vc_wreply)
                        && WriteReplyIsLargerThanVCInLocal(wp.msg.local, p.msg.vc_wreply)
}

predicate AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocals(
    b:Behavior<CMState>,
    i:int
)
    requires 0 < i 
    requires IsValidBehaviorPrefix(b, i)
{
    lemma_BehaviorValidImpliesOneStepValid(b, i);

    forall p :: p in b[i].environment.sentPackets && p.msg.Message_Write_Reply? ==> WriteReplyHasCorrspondingWriteWithSmallerVC(b, i, p)
}

predicate ReadReplyVCIsLargerThanAllPreviousWrites(
    b:Behavior<CMState>,
    i:int,
    p:Packet
)
    requires 0 < i 
    requires IsValidBehaviorPrefix(b, i)
    requires p in b[i].environment.sentPackets && p.msg.Message_Read_Reply? && PacketValid(p)
{
    lemma_BehaviorValidImpliesOneStepValid(b, i);
    forall wrp :: wrp in b[i].environment.sentPackets && wrp.msg.Message_Write_Reply?
            && p.msg.key_rreply == wrp.msg.key_wreply
            && (VCHappendsBefore(wrp.msg.vc_wreply, p.msg.vc_rreply) || VCEq(wrp.msg.vc_wreply, p.msg.vc_rreply))
                ==> WriteReplyHasCorrspondingWriteWithSmallerVC(b, i, wrp)
}

lemma lemma_WriteReplyHasHigerVCThanDepsAndLocalPrefix(
    b:Behavior<CMState>,
    i:int
)
    requires 0 < i 
    requires IsValidBehaviorPrefix(b, i)
    requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    // ensures AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocals(b, i)
    decreases i
{
    if i <= i {
        return;
    }

    lemma_ConstantsAllConsistent(b, i-1);
    lemma_ConstantsAllConsistent(b, i);

    if !StepSendsWriteReply(b[i-1], b[i]){
        lemma_WriteReplyHasHigerVCThanDepsAndLocalPrefix(b, i-1);
        return;
    }

    lemma_WriteReplyHasHigerVCThanDepsAndLocalPrefix(b, i-1);

    var p :| p in b[i].environment.sentPackets && p !in b[i-1].environment.sentPackets && p.msg.Message_Write_Reply?;

    assert PacketValid(p);

    var idx, ios := lemma_ActionThatSendsWriteReplyIsServerReceiveWrite(b[i-1], b[i], p);

    var p_write := ios[0].r;
    var sp := ExtractSentPacketsFromIos(ios);

    assert ReceiveWrite(b[i-1].servers[idx].s, b[i].servers[idx].s, p_write, sp);
}

predicate StepSendsWriteReply(s:CMState, s':CMState)
    requires CMNext(s, s')
{
    // && s.environment.nextStep.LEnvStepHostIos?
    && exists p :: p in s'.environment.sentPackets && p.msg.Message_Write_Reply? && p !in s.environment.sentPackets
}

lemma lemma_ServerWriteReplyLargerVCThanLocalAndDeps(s:Server, s':Server, p:Packet, sp:seq<Packet>)
    requires p.msg.Message_Write?
    requires ServerValid(s)
    requires PacketValid(p) 
    requires ReceiveWrite(s, s', p, sp)
    ensures |sp| == 2
    ensures sp[0].msg.Message_Write_Reply?
    ensures forall k :: k in p.msg.local ==> 
                VCHappendsBefore(p.msg.local[k].vc, sp[0].msg.vc_wreply) || VCEq(p.msg.local[k].vc, sp[0].msg.vc_wreply)
    ensures forall k :: k in p.msg.deps_write ==> 
                VCHappendsBefore(p.msg.deps_write[k], sp[0].msg.vc_wreply) || VCEq(p.msg.deps_write[k], sp[0].msg.vc_wreply)
{
    assert forall k :: k in p.msg.local ==> MetaValid(p.msg.local[k]);
    var local_metas := set m | m in p.msg.local.Values;
    var vcs_local := set m | m in local_metas :: m.vc;
    assert forall vc :: vc in vcs_local ==> VectorClockValid(vc); 
    var merged_vc := FoldVC(s.gvc, vcs_local);
    assert forall vc :: vc in vcs_local ==> VCHappendsBefore(vc, merged_vc) || VCEq(vc, merged_vc);
    assert forall m :: m in local_metas ==> VCHappendsBefore(m.vc, merged_vc) || VCEq(m.vc, merged_vc);
    assert forall k :: k in p.msg.local ==> p.msg.local[k] in local_metas;
    assert forall k :: k in p.msg.local ==> 
                VCHappendsBefore(p.msg.local[k].vc, sp[0].msg.vc_wreply) || VCEq(p.msg.local[k].vc, sp[0].msg.vc_wreply);

    var vcs_deps := set k | k in p.msg.deps_write :: p.msg.deps_write[k];
    var merged_vc2 := FoldVC(merged_vc, vcs_deps);
    assert forall vc :: vc in vcs_deps ==> VCHappendsBefore(vc, merged_vc2) || VCEq(vc, merged_vc2);
    assert forall k :: k in p.msg.deps_write ==> 
                VCHappendsBefore(p.msg.deps_write[k], merged_vc2) || VCEq(p.msg.deps_write[k], merged_vc2);
    assert forall k :: k in p.msg.deps_write ==> 
                VCHappendsBefore(p.msg.deps_write[k], sp[0].msg.vc_wreply) || VCEq(p.msg.deps_write[k], sp[0].msg.vc_wreply);
}

}