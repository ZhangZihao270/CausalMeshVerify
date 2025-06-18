include "Constants.i.dfy"
include "Message.i.dfy"
include "Broadcast.i.dfy"
include "../../Common/Collections/Maps.i.dfy"
include "../Common/UpperBound.s.dfy"
module LiveTPC__Coordinator_i {
import opened LiveTPC__Types_i
import opened LiveTPC__Constants_i
import opened LiveTPC__Message_i
import opened Concrete_NodeIdentity_i
import opened LiveTPC__Broadcast_i
import opened AppStateMachine_s
import opened Collections__Maps_i
import opened Environment_s
import opened Common__UpperBound_s

type Votes = map<NodeIdentity, TpcPacket>

datatype RequestStateTuple = RequestStateTuple(req:Request, votes:Votes)

datatype OperationToBeDecided = OperationToBeDecided(v:Request, votes:seq<int>) | OpUnknown() 

datatype DecisionToSend = DecisionToSend(opn:int, req:Request, rep:Reply) | DecisionUnknown()

datatype Coordinator = Coordinator(
    constants : HostConstants,
    is_coor : bool,
    request_queue : seq<Request>,
    next_opn : int,
    opn_complete : int,
    next_op_to_be_decided : OperationToBeDecided,
    decision_to_be_send : DecisionToSend,
    request_states : map<int, RequestStateTuple>
    // ghost history : seq<CoordinatorHistoryEntry>
    // votes : map<TxnNumber, Votes>,
    // decision_reply : map<TxnNumber, set<NodeIdentity>>,
    // reply_cache : ReplyCache
)


predicate RequestsMatch(r1:Request, r2:Request)
{
  r1.Request? && r2.Request? && r1.client == r2.client && r1.tid == r2.tid
}

predicate ReceivedAllVotes(servers:seq<NodeIdentity>, votes:Votes)
{
    && (|servers| == |votes|)
    && (forall i :: i in servers ==> i in votes)
    && (forall i :: i in votes ==> votes[i].msg.VoteMsg?)
}

function ConvertVotePacketMapToVotePacketSequence(servers:seq<NodeIdentity>, votes:Votes):seq<TpcPacket>
    requires forall i :: i in servers ==> i in votes
    requires forall i :: i in votes ==> votes[i].msg.VoteMsg?
    ensures forall p :: p in ConvertVotePacketMapToVotePacketSequence(servers, votes) ==> p.msg.VoteMsg?
    ensures |servers| == |ConvertVotePacketMapToVotePacketSequence(servers, votes)|
    ensures var vote_seq := ConvertVotePacketMapToVotePacketSequence(servers, votes);
            forall v :: v in vote_seq ==> exists n :: n in votes && votes[n] == v
{
    if |servers| == 0 then
        []
    else
        var vote := votes[servers[0]];
        [vote] + ConvertVotePacketMapToVotePacketSequence(servers[1..], votes)
}

function ConvertVotePacketsToVoteSeqs(packets:seq<TpcPacket>) : seq<int>
    requires forall p :: p in packets ==> p.msg.VoteMsg?
    ensures |packets| == |ConvertVotePacketsToVoteSeqs(packets)|
    ensures forall v :: v in ConvertVotePacketsToVoteSeqs(packets) ==> exists p :: p in packets && p.msg.vote == v
{
    if |packets| == 0 then
        []
    else
        var p := packets[0];
        var packets_rest := packets[1..];
        var votes := ConvertVotePacketsToVoteSeqs(packets_rest);
        [p.msg.vote] + votes
}

predicate AllVotesAreYes(votes:seq<int>)
{
  forall v :: v in votes ==> v == 0
}

function CoorMakeDecision(votes:seq<int>) : int
{
  if AllVotesAreYes(votes) then
    1
  else
    2
}

function CoordinatorGenerateReply(req:Request, decision:int) : Reply
{
    if decision == 1 then
        Reply(req.client, req.tid, Commit())
    else
        Reply(req.client, req.tid, Abort())
}

predicate CoordinatorCanNominateUsingOpn(s:Coordinator, opn:int)
{
    && s.is_coor == true
    && LtUpperBound(opn, s.constants.all.params.max_integer_val)
}

predicate CoordinatorInit(coor:Coordinator,c:HostConstants)
{
    && coor.constants == c
    && coor.request_queue == []
    && coor.next_opn == 0
    && coor.opn_complete == 0
    && coor.request_states == map[]
    && coor.next_op_to_be_decided == OpUnknown()
    && coor.decision_to_be_send == DecisionUnknown()
    && if coor.constants.my_index == coor.constants.all.params.coor_id then coor.is_coor == true else coor.is_coor == false
}

predicate CoordinatorProcessRequest(s:Coordinator, s':Coordinator, packet:TpcPacket, sent_packets:seq<TpcPacket>)
    requires packet.msg.RequestMsg?
{
    var opn := s.next_opn;
    var tid := packet.msg.tid;
    var nreq := Request(packet.src, tid, packet.msg.req);
    // check whether the req is exists in request queue or request states?
    if exists req :: req in s.request_queue && RequestsMatch(req, nreq) then
        && s' == s 
        && sent_packets == []
    else if && CoordinatorCanNominateUsingOpn(s, opn) then
        var tup := RequestStateTuple(nreq, map[]);
        && s' == s.(next_opn := s.next_opn + 1, 
                    request_queue := s.request_queue + [nreq],
                    request_states := s.request_states[opn := tup]
                    )
        && LBroadcastToEveryone(s.constants.all.config, s.constants.my_index, VoteReqMsg(opn, s.constants.my_index, nreq), sent_packets)
    else
        && s' == s 
        && sent_packets == []
}

predicate CoordinatorProcessVote(s:Coordinator, s':Coordinator, packet:TpcPacket)
    requires packet.msg.VoteMsg?
{
    var m := packet.msg;
    var opn := m.opn_vote;
    if packet.src !in s.constants.all.config.node_ids then
        s' == s
    else if opn !in s.request_states then
        s' == s
    else if 
            && opn in s.request_states 
            && packet.src !in s.request_states[opn].votes  then
        var tup := s.request_states[opn];
        var tup' := tup.(votes := tup.votes[packet.src := packet]);

        s' == s.(request_states := s.request_states[opn := tup'])
    else
        s' == s
}

predicate CoordinatorGetDecision(s:Coordinator, s':Coordinator, opn:int, v:Request, votes:seq<int>)
    requires opn == s.opn_complete
    requires s.next_op_to_be_decided.OpUnknown?
{
    s' == s.(next_op_to_be_decided := OperationToBeDecided(v, votes))
}

predicate CoordinatorMakeDecision(s:Coordinator, s':Coordinator, sent_packets:seq<TpcPacket>)
    requires s.next_op_to_be_decided.OperationToBeDecided?
    requires s.opn_complete in s.request_states
    requires HostConstantsValid(s.constants)
{
    var opn := s.opn_complete;
    var req := s.next_op_to_be_decided.v;
    var tid := req.tid;
    var votes := s.next_op_to_be_decided.votes;
    var dec := CoorMakeDecision(votes);
    var reply := CoordinatorGenerateReply(req, dec);

    && s' == s.(next_op_to_be_decided := OpUnknown(), 
                decision_to_be_send := DecisionToSend(opn, req, reply), 
                request_states := RemoveElt(s.request_states, opn),
                opn_complete := s.opn_complete + 1)
    && sent_packets == [LPacket(req.client, s.constants.all.config.node_ids[s.constants.my_index], ReplyMsg(reply.tid, reply.rep))]
}

// todo: remove req from request_queue
predicate CoordinatorMaybeEnterCommitPhase(s:Coordinator, s':Coordinator, sent_packets:seq<TpcPacket>)
{
    if s.decision_to_be_send.DecisionToSend? then
        var opn := s.decision_to_be_send.opn;
        var req := s.decision_to_be_send.req;
        var rep := s.decision_to_be_send.rep;
        && s' == s.(decision_to_be_send := DecisionUnknown())
        && LBroadcastToEveryone(s.constants.all.config, s.constants.my_index, DecisionMsg(opn, req.tid, rep), sent_packets)
    else
        && s' == s
        && sent_packets == []
}

}