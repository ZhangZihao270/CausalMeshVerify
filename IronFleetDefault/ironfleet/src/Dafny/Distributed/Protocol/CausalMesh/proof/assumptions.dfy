include "../distributed_system.dfy"
include "../../../Common/Collections/Maps2.i.dfy"

module CausalMesh_proof_Assumptions_i {
import opened CausalMesh_Cache_i
import opened CausalMesh_Message_i
import opened CausalMesh_Types_i
import opened Environment_s
import opened CausalMesh_DistributedSystem_i
import opened Temporal__Temporal_s
import opened Collections__Maps2_s

predicate IsValidBehaviorPrefix(
  b:Behavior<CMState>,
  i:int
  )
{
  && imaptotal(b)
  && CMInit(b[0])
  && (forall j {:trigger CMNext(b[j], b[j+1])} :: 0 <= j < i ==> CMNext(b[j], b[j+1]))
}

}