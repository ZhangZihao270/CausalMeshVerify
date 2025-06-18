include "../DistributedSystem.i.dfy"
include "Decide.i.dfy"
include "Assumptions.i.dfy"
include "Constants.i.dfy"
include "MessageVote.i.dfy"
include "Environment.i.dfy"
include "PacketSending.i.dfy"

module TpcRefinement__Requests_i {
import opened Temporal__Temporal_s
import opened LiveTPC__DistributedSystem_i
import opened LiveTPC__Constants_i
import opened LiveTPC__Types_i
import opened LiveTPC__Message_i
import opened LiveTPC__Host_i
import opened LiveTPC__Coordinator_i
import opened TpcRefinement__Decide_i
import opened TpcRefinement__Assumptions_i
import opened TpcRefinement__Constants_i
import opened TpcRefinement__MessageVote_i
import opened TpcRefinement__Environment_i
import opened TpcRefinement__PacketSending_i
import opened TpcRefinement__Actions_i
import opened Concrete_NodeIdentity_i

lemma lemma_RequestInVoteReqMessageHasCorrespondingRequestMessage(
    b:Behavior<TpcState>,
    c:Constants,
    i:int,
    p_vote_req:TpcPacket
    // req_num:int
)
returns
(
    p_req:TpcPacket
)
    requires IsValidBehaviorPrefix(b, c, i)
    requires 0 <= i 
    requires p_vote_req in b[i].environment.sentPackets
    requires p_vote_req.src in c.config.node_ids
    requires p_vote_req.msg.VoteReqMsg?
    // requires 0 <= req_num < |p_vote_req.msg.|
    ensures p_req in b[i].environment.sentPackets
    ensures p_req.dst in c.config.node_ids
    ensures p_req.msg.RequestMsg?
    ensures p_vote_req.msg.request == Request(p_req.src, p_req.msg.tid, p_req.msg.req)
    decreases i, 0
{
    if i == 0
    {
        return;
    }

    if p_vote_req in b[i-1].environment.sentPackets
    {
        p_req := lemma_RequestInVoteReqMessageHasCorrespondingRequestMessage(b, c, i-1, p_vote_req);
        lemma_PacketStaysInSentPackets(b, c, i-1, i, p_req);
        return;
    }

    lemma_ConstantsAllConsistent(b, c, i-1);
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_AssumptionsMakeValidTransition(b, c, i-1);

    var idx, ios := lemma_ActionThatSendsVoteReqIsProcessRequest(b[i-1], b[i], p_vote_req);

    // var s := b[i-1].hosts[idx].host.coordinator;
    // var s' := b[i].hosts[idx].host.coordinator;
    // var sent_packets := ExtractSentPacketsFromIos(ios);

    // assert CoordinatorCanNominateUsingOpn(s, s.next_opn);
    p_req := ios[0].r;
    // var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
}

lemma lemma_DecidedRequestWasSentByCLient(
    b:Behavior<TpcState>,
    c:Constants,
    i:int,
    qs:seq<QuorumOfVotes>,
    reqs:seq<Request>,
    req_num:int
)
returns 
(
    p:TpcPacket
)
    requires IsValidBehaviorPrefix(b, c, i)
    requires 0 <= i 
    requires IsValidQuorumOfVotesSequence(b[i], qs)
    requires reqs == GetSequenceOfRequest(qs)
    requires 0 <= req_num < |reqs|
    ensures p in b[i].environment.sentPackets
    ensures p.dst in c.config.node_ids
    ensures p.msg.RequestMsg?
    ensures reqs[req_num] == Request(p.src, p.msg.tid, p.msg.req)
    decreases i
{
    lemma_ConstantsAllConsistent(b, c, i);

    lemma_SequenceOfRequestsNthElement(qs, req_num);
    var req := reqs[req_num];
    var q := qs[req_num];
    var idx :| idx in q.indices;
    var packet_vote := q.packets[idx];
    assert packet_vote.msg.VoteMsg?;
    assert packet_vote.msg.request == req;

    var packet_vote_request := lemma_VoteMessageHasCorrespondingVoteReqMessage(b, c, i, packet_vote);
    // assert req.tid == packet_vote_request.msg.request.tid as int;
    assert packet_vote.msg.request == packet_vote_request.msg.request;

    p := lemma_RequestInVoteReqMessageHasCorrespondingRequestMessage(b, c, i, packet_vote_request);
    assert packet_vote_request.msg.request == Request(p.src, p.msg.tid, p.msg.req);
}
}