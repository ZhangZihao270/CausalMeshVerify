include "../../Common/Framework/Main.s.dfy"
include "../../Protocol/TPC/RefinementProof/Refinement.i.dfy"
include "../../Protocol/Common/NodeIdentity.i.dfy"
include "AbstractService.s.dfy"

module Main_i refines Main_s {
import opened Native__NativeTypes_s
import opened TpcRefinement__DistributedSystem_i
import opened TpcRefinement__Refinement_i

// lemma lemma_RefinementProofForFixedBehavior(c:Constants, pb:seq<TpcState>) returns (sb:seq<ServiceState>)
// {
//     var rs := lemma_GetBehaviorRefinement(pb, c);
//     sb := RenameToServiceStates(rs);
// }
}