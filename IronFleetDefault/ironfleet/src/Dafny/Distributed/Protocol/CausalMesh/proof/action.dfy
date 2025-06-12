include "../distributed_system.dfy"
include "../../../Common/Logic/Temporal/Rules.i.dfy"
include "constants.dfy"

module CausalMesh_Proof_Actions_i {
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

  lemma lemma_ActionThatChangesServerIsThatServersAction(
    b:Behavior<CMState>,
    i:int,
    idx:int
  )
    returns (ios:seq<CMIo>)
    requires IsValidBehaviorPrefix(b, i+1)
    requires 0 <= i
    requires 0 <= idx < |b[i].servers|
    requires 0 <= idx < |b[i+1].servers|
    requires b[i+1].servers[idx] != b[i].servers[idx]
    ensures  b[i].environment.nextStep.LEnvStepHostIos?
    ensures  0 <= idx < Nodes
    ensures  b[i].environment.nextStep.actor == idx
    ensures  ios == b[i].environment.nextStep.ios
    ensures  CMNext(b[i], b[i+1])
    ensures  CMNextServer(b[i], b[i+1], idx, ios)
  {
    lemma_AssumptionsMakeValidTransition(b, i);
    // lemma_ConstantsAllConsistent(b, i);
    assert CMNext(b[i], b[i+1]);
    ios :| CMNextServer(b[i], b[i+1], idx, ios);
  }

}