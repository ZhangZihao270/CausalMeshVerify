include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Constants.i.dfy"
include "Environment.i.dfy"
include "PacketSending.i.dfy"

module TpcRefinement__MessageVote_i {
import opened LiveTPC__Constants_i
import opened LiveTPC__DistributedSystem_i
import opened LiveTPC__Message_i
import opened LiveTPC__Host_i
import opened LiveTPC__Participant_i
import opened TpcRefinement__Assumptions_i
import opened TpcRefinement__Environment_i
import opened TpcRefinement__Constants_i
import opened TpcRefinement__PacketSending_i
import opened Temporal__Temporal_s

lemma lemma_VoteMessageHasCorrespondingVoteReqMessage(
    b:Behavior<TpcState>,
    c:Constants,
    i:int,
    p_vote:TpcPacket
)
returns
(
    p_vote_req:TpcPacket
)
    requires IsValidBehaviorPrefix(b, c, i)
    requires 0 <= i 
    requires p_vote in b[i].environment.sentPackets
    requires p_vote.src in c.config.node_ids
    requires p_vote.msg.VoteMsg?
    ensures p_vote_req in b[i].environment.sentPackets
    ensures p_vote_req.src in c.config.node_ids
    ensures p_vote_req.msg.VoteReqMsg?
    ensures p_vote_req.msg.opn_votereq == p_vote.msg.opn_vote
    ensures p_vote_req.msg.request == p_vote.msg.request
    ensures p_vote_req.msg.coor_id == p_vote.msg.coor_id
    ensures p_vote.msg.vote == ParticipantMakeVote(p_vote_req.msg.request.req)
    ensures p_vote.msg.vote == ParticipantMakeVote(p_vote.msg.request.req)
    decreases i
{
    if i == 0
    {
        return;
    }

    if p_vote in b[i-1].environment.sentPackets
    {
        p_vote_req := lemma_VoteMessageHasCorrespondingVoteReqMessage(b, c, i-1, p_vote);
        lemma_PacketStaysInSentPackets(b, c, i-1, i, p_vote_req);
        return;
    }

    lemma_AssumptionsMakeValidTransition(b, c, i-1);
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_ConstantsAllConsistent(b, c, i-1);

    var idx, ios := lemma_ActionThatSendsVoteIsProcessVoteReq(b[i-1], b[i], p_vote);
    p_vote_req := ios[0].r;
}
}