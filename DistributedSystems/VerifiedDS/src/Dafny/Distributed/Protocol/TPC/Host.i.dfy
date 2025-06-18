include "Coordinator.i.dfy"
include "Participant.i.dfy"

module LiveTPC__Host_i {
import opened LiveTPC__Coordinator_i
import opened LiveTPC__Participant_i
import opened LiveTPC__Types_i
import opened LiveTPC__Constants_i
import opened LiveTPC__Configuration_i
import opened LiveTPC__Message_i
import opened Environment_s
datatype Host = Host (
    constants:HostConstants,
    coordinator:Coordinator,
    participant:Participant
)

predicate HostInit(s:Host, c:HostConstants)
    requires WellFormedLConfiguration(c.all.config)
{
    && s.constants == c 
    && CoordinatorInit(s.coordinator, c)
    && ParticipantInit(s.participant, c)
}

predicate HostNextProcessRequest(s:Host, s':Host, packet:TpcPacket, sent_packets:seq<TpcPacket>)
    requires packet.msg.RequestMsg?
{
    var tid := packet.msg.tid;
        && CoordinatorProcessRequest(s.coordinator, s'.coordinator, packet, sent_packets)
        && s' == s.(coordinator := s'.coordinator)
}

predicate HostNextProcessVoteRequest(s:Host, s':Host, packet:TpcPacket, sent_packets:seq<TpcPacket>)
    requires packet.msg.VoteReqMsg?
{
    && ParticipantProcessVoteRequest(s.participant, s'.participant, packet, sent_packets)
    && s' == s.(participant := s'.participant)
}

predicate HostNextProcessVote(s:Host, s':Host, packet:TpcPacket, sent_packets:seq<TpcPacket>)
    requires packet.msg.VoteMsg?
{
    var opn := packet.msg.opn_vote;
    var learnable := s.coordinator.opn_complete < opn || (s.coordinator.opn_complete == opn && s.coordinator.next_op_to_be_decided.OpUnknown?);
    if learnable then
        && CoordinatorProcessVote(s.coordinator, s'.coordinator, packet)
        && s' == s.(coordinator := s'.coordinator)
        && sent_packets == []
    else
        s' == s && sent_packets == []
}

predicate HostNextMaybeMakeDecision(s:Host, s':Host, sent_packets:seq<TpcPacket>)
{
    var opn := s.coordinator.opn_complete;
    if opn in s.coordinator.request_states 
        && ReceivedAllVotes(s.coordinator.constants.all.config.node_ids, s.coordinator.request_states[opn].votes) 
        && s.coordinator.next_op_to_be_decided.OpUnknown? then
        var req := s.coordinator.request_states[opn].req;
        var vote_packets := ConvertVotePacketMapToVotePacketSequence(s.coordinator.constants.all.config.node_ids, s.coordinator.request_states[opn].votes);
        var votes := ConvertVotePacketsToVoteSeqs(vote_packets);
        && CoordinatorGetDecision(s.coordinator, s'.coordinator, opn, req, votes)
        && s' == s.(coordinator := s'.coordinator)
        && sent_packets == []
    else
        s' == s && sent_packets == []
}

predicate HostNextMakeDicision(s:Host, s':Host, sent_packets:seq<TpcPacket>)
{
    if s.coordinator.next_op_to_be_decided.OperationToBeDecided?
        && s.coordinator.opn_complete in s.coordinator.request_states
        && HostConstantsValid(s.coordinator.constants) then
        && CoordinatorMakeDecision(s.coordinator, s'.coordinator, sent_packets)
        && s' == s.(coordinator := s'.coordinator)
    else
        s' == s && sent_packets == []
}

predicate HostNextMaybeEnterCommitPhase(s:Host, s':Host, sent_packets:seq<TpcPacket>)
{
    && CoordinatorMaybeEnterCommitPhase(s.coordinator, s'.coordinator, sent_packets)
    && s' == s.(coordinator := s'.coordinator)
}

predicate HostNextProcessDecision(s:Host, s':Host, packet:TpcPacket, sent_packets:seq<TpcPacket>)
    requires packet.msg.DecisionMsg?
{
    && ParticipantProcessDecision(s.participant, s'.participant, packet, sent_packets)
    && s' == s.(participant := s'.participant)
}

predicate HostNextProcessReply(s:Host, s':Host, packet:TpcPacket, sent_packets:seq<TpcPacket>)
    requires packet.msg.ReplyMsg?
{
    s' == s && sent_packets == []
}

predicate HostNextProcessInvalid(s:Host, s':Host, packet:TpcPacket, sent_packets:seq<TpcPacket>)
    requires packet.msg.TpcMessage_Invalid?
{
    s' == s && sent_packets == []
}

function {:opaque} ExtractSentPacketsFromIos(ios:seq<TpcIo>) : seq<TpcPacket>
  ensures forall p :: p in ExtractSentPacketsFromIos(ios) <==> LIoOpSend(p) in ios
{
  if |ios| == 0 then
    []
  else if ios[0].LIoOpSend? then
    [ios[0].s] + ExtractSentPacketsFromIos(ios[1..])
  else
    ExtractSentPacketsFromIos(ios[1..])
}

predicate HostNextProcessPacketReal(s:Host, s':Host, ios:seq<TpcIo>)
  requires |ios| >= 1
  requires ios[0].LIoOpReceive?
{
    && (forall io :: io in ios[1..] ==> io.LIoOpSend?) // why
    && var sent_packets := ExtractSentPacketsFromIos(ios);
        match ios[0].r.msg
            case TpcMessage_Invalid => HostNextProcessInvalid(s, s', ios[0].r, sent_packets)
            case RequestMsg(_,_) => HostNextProcessRequest(s, s', ios[0].r, sent_packets)
            case VoteReqMsg(_,_,_) => HostNextProcessVoteRequest(s, s', ios[0].r, sent_packets)
            case VoteMsg(_,_,_,_) => HostNextProcessVote(s, s', ios[0].r, sent_packets)
            case DecisionMsg(_,_,_) => HostNextProcessDecision(s, s', ios[0].r, sent_packets)
            case ReplyMsg(_,_) => HostNextProcessReply(s, s', ios[0].r, sent_packets)
}

predicate HostNextProcessPacket(s:Host, s':Host, ios:seq<TpcIo>)
{
    && |ios| >= 1
    && if ios[0].LIoOpTimeoutReceive? then
        s' == s && |ios| == 1
      else
        (&& ios[0].LIoOpReceive?
        && HostNextProcessPacketReal(s, s', ios)
        )
}

predicate SpontaneousIos(ios:seq<TpcIo>)
{
  && (forall i :: 0<=i<|ios| ==> ios[i].LIoOpSend?)
}

predicate HostNoReceiveNext(s:Host, nextActionIndex:int, s':Host, ios:seq<TpcIo>)
{
    var sent_packets := ExtractSentPacketsFromIos(ios);
    if nextActionIndex == 1 then
        && SpontaneousIos(ios)
        && HostNextMaybeMakeDecision(s, s', sent_packets)
    else if nextActionIndex == 2 then
        && SpontaneousIos(ios)
        && HostNextMakeDicision(s, s', sent_packets)
    else
        && nextActionIndex == 3
        && SpontaneousIos(ios)
        && HostNextMaybeEnterCommitPhase(s, s', sent_packets)
}

datatype LScheduler = LScheduler(host:Host, nextActionIndex:int)

predicate LSchedulerInit(s:LScheduler, c:HostConstants)
    requires WellFormedLConfiguration(c.all.config)
{
    && HostInit(s.host, c)
    && s.nextActionIndex == 0
}

function LSchedulerNumActions() : int
{
  5
}

predicate LSchedulerNext(s:LScheduler, s':LScheduler, ios:seq<TpcIo>)
{
    && s'.nextActionIndex == (s.nextActionIndex + 1) % 3
    && if s.nextActionIndex == 0 then
        HostNextProcessPacket(s.host, s'.host, ios)
       else
        HostNoReceiveNext(s.host, s.nextActionIndex, s'.host, ios)
}
}