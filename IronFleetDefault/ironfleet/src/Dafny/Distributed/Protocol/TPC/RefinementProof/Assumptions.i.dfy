include "../DistributedSystem.i.dfy"

module TpcRefinement__Assumptions_i {
import opened LiveTPC__DistributedSystem_i
import opened LiveTPC__Message_i
import opened LiveTPC__Constants_i
import opened Temporal__Temporal_s
import opened Concrete_NodeIdentity_i
import opened Environment_s
import opened Collections__Maps2_s

predicate IsValidBehaviorPrefix(
    b:Behavior<TpcState>,
    c:Constants,
    i:int
)
{
    && imaptotal(b)
    && TpcInit(b[0], c)
    && (forall j {:trigger TpcNext(b[j], b[j+1])} :: 0 <= j < i ==> TpcNext(b[j], b[j+1]))
}

lemma {:axiom} idx_equal (i:int, j:int)
    ensures i == j

}