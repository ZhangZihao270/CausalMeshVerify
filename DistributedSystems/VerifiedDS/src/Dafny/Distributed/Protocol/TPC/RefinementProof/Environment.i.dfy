include "../DistributedSystem.i.dfy"
include "../../../Common/Logic/Temporal/Heuristics.i.dfy"
include "Assumptions.i.dfy"
include "Constants.i.dfy"

module TpcRefinement__Environment_i {
import opened LiveTPC__Constants_i
import opened LiveTPC__DistributedSystem_i
import opened LiveTPC__Message_i
import opened Temporal__Temporal_s
import opened Temporal__Heuristics_i
import opened Temporal__Rules_i
import opened TpcRefinement__Assumptions_i
import opened TpcRefinement__Constants_i
import opened Environment_s

lemma lemma_PacketStaysInSentPackets(
  b:Behavior<TpcState>,
  c:Constants,
  i:int,
  j:int,
  p:TpcPacket
  )
  requires IsValidBehaviorPrefix(b, c, j)
  requires 0 <= i <= j
  requires p in b[i].environment.sentPackets
  ensures  p in b[j].environment.sentPackets
{
  if j == i
  {
  }
  else
  {
    lemma_PacketStaysInSentPackets(b, c, i, j-1, p);
    lemma_AssumptionsMakeValidTransition(b, c, j-1);
  }
}

}