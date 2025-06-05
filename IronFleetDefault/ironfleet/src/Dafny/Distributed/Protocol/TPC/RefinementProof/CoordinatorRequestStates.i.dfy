include "../DistributedSystem.i.dfy"
include "Actions.i.dfy"
include "Assumptions.i.dfy"
include "Constants.i.dfy"
include "Environment.i.dfy"
include "MessageVote.i.dfy"
include "MessageVoteRequest.i.dfy"
include "PacketSending.i.dfy"

module TpcRefinement__CoordinatorRequestStates_i {
import opened LiveTPC__Configuration_i
import opened LiveTPC__Constants_i
import opened LiveTPC__DistributedSystem_i
import opened LiveTPC__Message_i
import opened LiveTPC__Participant_i
import opened TpcRefinement__Actions_i
import opened TpcRefinement__Assumptions_i
import opened TpcRefinement__Constants_i
import opened TpcRefinement__Environment_i
import opened TpcRefinement__MessageVote_i
import opened TpcRefinement__MessageVoteRequest_i
import opened TpcRefinement__PacketSending_i
import opened Temporal__Temporal_s
import opened Concrete_NodeIdentity_i

lemma {:axiom} lemma_idx_equal (i:int, j:int)
    ensures i == j
    
lemma lemma_ReceivedVoteMessageSenderAlwaysValidHosts(
    b:Behavior<TpcState>,
    c:Constants,
    i:int,
    coor_idx:int,
    opn:int
)
    requires IsValidBehaviorPrefix(b, c, i)
    requires 0 <= i 
    requires 0 <= coor_idx < |b[i].hosts|
    requires opn in b[i].hosts[coor_idx].host.coordinator.request_states
    ensures forall sender :: sender in b[i].hosts[coor_idx].host.coordinator.request_states[opn].votes
            ==> sender in c.config.node_ids
    decreases i
{
    if i == 0 
    {
        return;
    }

    lemma_AssumptionsMakeValidTransition(b, c, i-1);
    lemma_ConstantsAllConsistent(b, c, i-1);
    lemma_ConstantsAllConsistent(b, c, i);

    var s := b[i-1].hosts[coor_idx].host.coordinator;
    var s' := b[i].hosts[coor_idx].host.coordinator;

    forall sender | sender in s'.request_states[opn].votes 
        ensures sender in c.config.node_ids
    {
        if opn in s.request_states && sender in s.request_states[opn].votes 
        {
            lemma_ReceivedVoteMessageSenderAlwaysValidHosts(b, c, i-1, coor_idx, opn);
        }
        else 
        {
            var ios := lemma_ActionThatChangesHostIsThatHostsAction(b, c, i-1, coor_idx);
        }
    }
}

// lemma lemma_ReceivedVoteMessageSenderAlwaysNonempty(
//     b:Behavior<TpcState>,
//     c:Constants,
//     i:int,
//     coor_idx:int,
//     opn:int
// )
//     requires IsValidBehaviorPrefix(b, c, i)
//     requires 0 <= i 
//     requires 0 <= coor_idx < |b[i].hosts|
//     requires opn in b[i].hosts[coor_idx].host.coordinator.request_states
//     ensures |b[i].hosts[coor_idx].host.coordinator.request_states[opn].votes| > 0
//     decreases i
// {
//     if i == 0 
//     {
//         return;
//     }

//     lemma_AssumptionsMakeValidTransition(b, c, i-1);
//     lemma_ConstantsAllConsistent(b, c, i);
//     lemma_ConstantsAllConsistent(b, c, i-1);

//     var s := b[i-1].hosts[coor_idx].host.coordinator;
//     var s' := b[i].hosts[coor_idx].host.coordinator;

//     if s'.request_states == s.request_states
//     {
//         lemma_ReceivedVoteMessageSenderAlwaysNonempty(b, c, i-1, coor_idx, opn);
//         return;
//     }

//     var ios := lemma_ActionThatChangesHostIsThatHostsAction(b, c, i-1, coor_idx);
//     if opn in s.request_states
//     {
//         lemma_ReceivedVoteMessageSenderAlwaysNonempty(b, c, i-1, coor_idx, opn);
//     }
// }

// 找到coordinator存的votes对应的vote message
lemma lemma_GetSentVoteMessageFromRequestStates(
    b:Behavior<TpcState>,
    c:Constants,
    i:int,
    coor_idx:int,
    opn:int,
    sender:NodeIdentity
)
returns 
(
    sender_idx:int,
    p:TpcPacket
)
    requires IsValidBehaviorPrefix(b, c, i)
    requires 0 <= i 
    requires 0 <= coor_idx < |b[i].hosts|
    requires opn in b[i].hosts[coor_idx].host.coordinator.request_states
    requires |b[i].hosts[coor_idx].host.coordinator.request_states[opn].votes| > 0
    requires sender in b[i].hosts[coor_idx].host.coordinator.request_states[opn].votes
    ensures 0 <= sender_idx < |c.config.node_ids|
    ensures p in b[i].environment.sentPackets
    ensures p.src == sender == c.config.node_ids[sender_idx]
    ensures p.msg.VoteMsg?
    ensures p == b[i].hosts[coor_idx].host.coordinator.request_states[opn].votes[sender]
    ensures p.msg.opn_vote == opn
    ensures p.msg.coor_id == coor_idx
    ensures p.msg.request == b[i].hosts[coor_idx].host.coordinator.request_states[opn].req
    ensures p.msg.vote == b[i].hosts[coor_idx].host.coordinator.request_states[opn].votes[sender].msg.vote
    ensures p.msg.vote == ParticipantMakeVote(p.msg.request.req)
    decreases i
{
    if i == 0
    {
        return;
    }

    lemma_HostConstantsAllConsistent(b, c, i, coor_idx);
    lemma_HostConstantsAllConsistent(b, c, i-1, coor_idx);
    lemma_AssumptionsMakeValidTransition(b, c, i-1);

    var s := b[i-1].hosts[coor_idx].host.coordinator;
    var s' := b[i].hosts[coor_idx].host.coordinator;

    if s'.request_states == s.request_states
    {
        sender_idx, p := lemma_GetSentVoteMessageFromRequestStates(b, c, i-1, coor_idx, opn, sender);
        lemma_PacketStaysInSentPackets(b, c, i-1, i, p);
        return;
    }

    if && opn in s.request_states
       && sender in s.request_states[opn].votes
       && s'.request_states[opn].req == s.request_states[opn].req
    {
        sender_idx, p := lemma_GetSentVoteMessageFromRequestStates(b, c, i-1, coor_idx, opn, sender);
        lemma_PacketStaysInSentPackets(b, c, i-1, i, p);
        return;
    }

    var ios := lemma_ActionThatChangesHostIsThatHostsAction(b, c, i-1, coor_idx);
    assert ios[0].LIoOpReceive?;
    p := ios[0].r;
    lemma_idx_equal(p.msg.coor_id, coor_idx);
    assume p.msg.coor_id == coor_idx;
    // var idx1, ios1 := lemma_ActionThatSendsVoteIsProcessVoteReq(b[i-1], b[i], p);
    sender_idx := GetNodeIndex(p.src, c.config);

    // if p.msg.request != s'.request_states[opn].req || p.msg.coor_id != coor_idx
    // {
    if |s.request_states[opn].votes| > 0 
    {
        assert opn in s.request_states;
        // lemma_ReceivedVoteMessageSenderAlwaysNonempty(b, c, i-1, coor_idx, opn);
        assert |s.request_states[opn].votes| > 0;
        var sender2 :| sender2 in s.request_states[opn].votes;
        var sender2_idx, p2 := lemma_GetSentVoteMessageFromRequestStates(b, c, i-1, coor_idx, opn, sender2);

        var p_vote_req := lemma_VoteMessageHasCorrespondingVoteReqMessage(b, c, i, p);
        assert p.msg.vote == ParticipantMakeVote(p_vote_req.msg.request.req);
        assert p.msg.vote == ParticipantMakeVote(p.msg.request.req);
        var p2_vote_req := lemma_VoteMessageHasCorrespondingVoteReqMessage(b, c, i, p2);
        lemma_VoteReqMessagesFromSameOpnMatch(b, c, i, p_vote_req, p2_vote_req);
        assert p.msg.vote == ParticipantMakeVote(p.msg.request.req);
    }
    else
    {
        var p_vote_req := lemma_VoteMessageHasCorrespondingVoteReqMessage(b, c, i, p);
        assert p.msg.vote == ParticipantMakeVote(p_vote_req.msg.request.req);
        assert p.msg.vote == ParticipantMakeVote(p.msg.request.req);
        //找到发出p_vote_req的action，判断p_vote_req和coor的request_states中存的req一样

        assert p_vote_req.msg.opn_votereq in s.request_states;
        lemma_VoteReqMessageIsSentByProcessRequest(b, c, i, coor_idx, p_vote_req);
    }
    // }
    // assert p.msg.vote == ParticipantMakeVote(p_vote_req.msg.request.req);
}
}