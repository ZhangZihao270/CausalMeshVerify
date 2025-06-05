include "Configuration.i.dfy"
include "Message.i.dfy"
include "../../Common/Framework/Environment.s.dfy"

module LiveTPC__Broadcast_i {
import opened LiveTPC__Message_i
import opened LiveTPC__Configuration_i
import opened Environment_s

predicate LBroadcastToEveryone(c:Configuration, myidx:int, m:TpcMessage, sent_packets:seq<TpcPacket>)
{
  && |sent_packets| == |c.node_ids|
  && 0 <= myidx < |c.node_ids|
  && forall idx ::
      0 <= idx < |sent_packets| ==> sent_packets[idx] == LPacket(c.node_ids[idx], c.node_ids[myidx], m)
}

} 
