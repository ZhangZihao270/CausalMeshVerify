include "../distributed_system.dfy"
// include "causalcut.dfy"
include "packet_sending.dfy"
include "properties.dfy"
include "read_reply_is_met.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module CausalMesh_Proof_ReadDepsIsMet_i {
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
import opened CausalMesh_Proof_DepsAreMet_i
import opened CausalMesh_Proof_ReadReplyIsMet_i
import opened Collections__Seqs_s
import opened Collections__Maps_i
import opened Collections__Maps2_s

lemma lemma_ReadDepsIsMetPrefix(
    b:Behavior<CMState>,
    i:int
)
    requires 0 < i 
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    decreases i
{

}

}