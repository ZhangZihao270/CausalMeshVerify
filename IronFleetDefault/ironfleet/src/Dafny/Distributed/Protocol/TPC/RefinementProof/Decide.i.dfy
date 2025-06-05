include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "StateMachine.i.dfy"
include "Constants.i.dfy"
include "Environment.i.dfy"
include "HandleRequest.i.dfy"
include "MessageVote.i.dfy"
include "MessageVoteRequest.i.dfy"
include "Actions.i.dfy"
include "CoordinatorRequestStates.i.dfy"
include "Quorum.i.dfy"

module TpcRefinement__Decide_i {
import opened LiveTPC__Types_i
import opened LiveTPC__Constants_i
import opened LiveTPC__Message_i
import opened LiveTPC__Coordinator_i
import opened LiveTPC__Host_i
import opened LiveTPC__Participant_i
import opened LiveTPC__Configuration_i
import opened LiveTPC__DistributedSystem_i
import opened Collections__Seqs_s
import opened Collections__Sets_i
import opened Temporal__Temporal_s
import opened TpcRefinement__Assumptions_i
import opened TpcRefinement__DistributedSystem_i
import opened TpcRefinement__Constants_i
import opened TpcRefinement__Environment_i
import opened TpcRefinement__HandleRequest_i
import opened TpcRefinement__MessageVote_i
import opened TpcRefinement__MessageVoteRequest_i
import opened TpcRefinement__Actions_i
import opened TpcRefinement__CoordinatorRequestStates_i
import opened TpcRefinement__Quorum_i
// import opened TpcRefinement__Request_i
import opened Concrete_NodeIdentity_i
import opened Environment_s
import opened AppStateMachine_s

datatype QuorumOfVotes = QuorumOfVotes(c:Constants, indices:set<int>, packets:seq<TpcPacket>, coor:int, opn:int, tid:TxnNumber, v:Request)


// function GetReplyFromVotes(reqs:seq<Request>, votes:seq<Votes>, i:int) : Reply
//     requires |reqs| == |votes|
//     requires 0 <= i < |reqs|
// {
//     var decision := CoordinatorMakeDecision(votes[i]);
//     CoordinatorGenerateReply(reqs[i], decision)
// }

// function ConvertVoteMsgPacketsToVoteSeqs(packets:seq<TpcPacket>) : seq<int>
//     requires forall p :: p in packets ==> p.msg.VoteMsg?
//     // requires forall i, j :: i in packets && j in packets && i.src == j.src ==> i == j
   
// {
//     if |packets| == 0 then
//         []
//     else
//         var p := packets[0];
//         var packets_rest := packets[1..];
//         var votes := ConvertVoteMsgPacketsToVoteSeqs(packets_rest);
//         [p.msg.vote] + votes
// }

function GetReplyFromVotes(reqs:seq<Request>, votes:seq<seq<int>>, i:int) : Reply
    requires |reqs| == |votes|
    requires 0 <= i < |reqs|
{
    var decision := CoorMakeDecision(votes[i]);
    CoordinatorGenerateReply(reqs[i], decision)
}

lemma lemma_NodesNotEmpty(ps:TpcState)
    ensures |ps.constants.config.node_ids| > 0

predicate IsValidQuorumOfVotes(
    ps:TpcState,
    q:QuorumOfVotes
)
{
    lemma_NodesNotEmpty(ps);
    && |q.indices| == |ps.constants.config.node_ids|
    && |q.indices| > 0
    // var coor := ps.hosts[ps.constants.params.coor_id].host.coordinator;
    // && |q.indices| == NodesSize(ps.constants.config)
    && |q.packets| == |ps.constants.config.node_ids|
    && q.v.tid == q.tid
    && q.c == ps.constants
    && q.coor == q.c.params.coor_id
    // && q.v == coor.request_states[q.opn].req
    && (forall idx :: idx in q.indices ==> && 0 <= idx < |ps.constants.config.node_ids|
                                        && var p := q.packets[idx];
                                        && p.src == ps.constants.config.node_ids[idx]
                                        && p.msg.VoteMsg?
                                        && p.msg.opn_vote == q.opn
                                        && p.msg.request == q.v
                                        && p.msg.coor_id == q.coor
                                        && p in ps.environment.sentPackets)
    && QuorumOfVotesAllVoteMsgs(q)
}

predicate QuorumOfVotesAllVoteMsgs(
    q:QuorumOfVotes
)
{
    forall p :: p in q.packets ==> p.msg.VoteMsg?
}

predicate IsValidQuorumOfVotesSequence(ps:TpcState, qs:seq<QuorumOfVotes>)
{
    forall i :: 0 <= i < |qs| ==> qs[i].opn == i && IsValidQuorumOfVotes(ps, qs[i]) 
}

predicate IsMaximalQuorumOfVoteSequence(ps:TpcState, qs:seq<QuorumOfVotes>)
{
    && IsValidQuorumOfVotesSequence(ps, qs)
    && !exists q :: IsValidQuorumOfVotes(ps, q) && q.opn == |qs|
}

function GetSequenceOfRequest(qs:seq<QuorumOfVotes>):seq<Request>
    ensures |GetSequenceOfRequest(qs)| == |qs|
{
    if |qs| == 0 then
        []
    else
        GetSequenceOfRequest(all_but_last(qs)) + [last(qs).v]
}

function GetSequenceOfVotes(qs:seq<QuorumOfVotes>):seq<seq<int>>
    requires forall q :: q in qs ==> QuorumOfVotesAllVoteMsgs(q)
    ensures |GetSequenceOfVotes(qs)| == |qs|
{
    assert forall q :: q in qs ==> forall p :: p in q.packets ==> p.msg.VoteMsg?;
    if |qs| == 0 then
        []
    else
        GetSequenceOfVotes(all_but_last(qs)) + [ConvertVotePacketsToVoteSeqs(last(qs).packets)]
}

lemma lemma_GetUpperBoundOnQuorumOfVotesOpn(
    b:Behavior<TpcState>,
    c:Constants,
    i:int
)
returns (
    bound:int
)
    requires IsValidBehaviorPrefix(b, c, i)
    ensures bound >= 0
    ensures !exists q :: IsValidQuorumOfVotes(b[i], q) && q.opn == bound
{
    var opns := set p | p in b[i].environment.sentPackets && p.msg.VoteMsg? :: p.msg.opn_vote;
    bound := if |opns| > 0 && intsetmax(opns) >= 0 then intsetmax(opns) + 1 else 1;
    if exists q :: IsValidQuorumOfVotes(b[i], q) && q.opn == bound
    {
        var q :| IsValidQuorumOfVotes(b[i], q) && q.opn == bound;
        assert |q.indices| > 0;
        var idx :| idx in q.indices;
        var p := q.packets[idx];
        assert p.msg.opn_vote in opns;
        assert p.msg.opn_vote > intsetmax(opns);
        assert p.msg.opn_vote in opns;
        assert false;
    }
}

lemma lemma_GetMaximalQuorumOfVotesSequenceWithinBound(
    b:Behavior<TpcState>,
    c:Constants,
    i:int,
    bound:int
)
returns 
(
    qs:seq<QuorumOfVotes>
)
    requires IsValidBehaviorPrefix(b, c, i)
    requires 0 <= bound
    ensures IsValidQuorumOfVotesSequence(b[i], qs)
    ensures |qs| == bound || !exists q :: IsValidQuorumOfVotes(b[i], q) && q.opn == |qs|
    // ensures forall i :: 0 <= i < bound ==> qs[i].v == b[i].hosts
    // ensures var coor := b[i].hosts[c.params.coor_id].host.coordinator; 
    //         coor.request_states[bound].req == qs[|qs|-1].v
{
    if bound == 0
    {
        qs := [];
        return;
    }

    qs := lemma_GetMaximalQuorumOfVotesSequenceWithinBound(b, c, i, bound - 1);
    if !exists q :: IsValidQuorumOfVotes(b[i], q) && q.opn == |qs|
    {
        return;
    }

    assert |qs| == bound - 1;
    var q :| IsValidQuorumOfVotes(b[i], q) && q.opn == bound - 1;
    qs := qs + [q];
}

lemma lemma_GetMaximalQuorumOfVotes(
    b:Behavior<TpcState>,
    c:Constants,
    i:int
)
returns (
    qs:seq<QuorumOfVotes>
)
    requires IsValidBehaviorPrefix(b, c, i)
    ensures IsMaximalQuorumOfVoteSequence(b[i], qs)
{
    var bound := lemma_GetUpperBoundOnQuorumOfVotesOpn(b, c, i);
    qs := lemma_GetMaximalQuorumOfVotesSequenceWithinBound(b, c, i, bound);
}

lemma lemma_IfValidQuorumOfVotesSequenceNowThenNext(
    b:Behavior<TpcState>,
    c:Constants,
    i:int,
    qs:seq<QuorumOfVotes>
)
    requires IsValidBehaviorPrefix(b, c, i+1)
    requires 0 <= i 
    requires IsValidQuorumOfVotesSequence(b[i], qs)
    ensures IsValidQuorumOfVotesSequence(b[i+1], qs)
{
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_ConstantsAllConsistent(b, c, i+1);

    forall opn | 0 <= opn < |qs|
        ensures qs[opn].opn == opn
        ensures IsValidQuorumOfVotes(b[i+1], qs[opn])
    {
        assert qs[opn].opn == opn && IsValidQuorumOfVotes(b[i], qs[opn]);
        forall idx | idx in qs[opn].indices
            ensures qs[opn].packets[idx] in b[i+1].environment.sentPackets
        {
            lemma_PacketStaysInSentPackets(b, c, i, i+1, qs[opn].packets[idx]);
        }
    }
}

lemma lemma_SequenceOfRequestsNthElement(qs:seq<QuorumOfVotes>, n:int)
    requires 0 <= n < |qs|
    ensures GetSequenceOfRequest(qs)[n] == qs[n].v
{
    if n < |qs| - 1
    {
        lemma_SequenceOfRequestsNthElement(all_but_last(qs), n);
    }
}

// lemma lemma_CoordinatorIsFixed

lemma lemma_DecideQuorumsMatchValue(
    b:Behavior<TpcState>,
    c:Constants,
    i:int,
    q1:QuorumOfVotes,
    q2:QuorumOfVotes
)
    requires IsValidBehaviorPrefix(b, c, i)
    requires 0 <= i 
    requires IsValidQuorumOfVotes(b[i], q1)
    requires IsValidQuorumOfVotes(b[i], q2)
    requires q1.opn == q2.opn
    // requires q1.coor == q2.coor
    ensures q1.v == q2.v
{
    lemma_ConstantsAllConsistent(b, c, i);

    var idx1 :| idx1 in q1.indices;
    var idx2 :| idx2 in q2.indices;
    var p1_vote := q1.packets[idx1];
    var p2_vote := q2.packets[idx2];
    // assert p1_vote.msg.coor_id == p2_vote.msg.coor_id;
    var p1_vote_req := lemma_VoteMessageHasCorrespondingVoteReqMessage(b, c, i, p1_vote);
    var p2_vote_req := lemma_VoteMessageHasCorrespondingVoteReqMessage(b, c, i, p2_vote);
    assert p1_vote_req.msg.coor_id == p2_vote_req.msg.coor_id;

    lemma_VoteReqMessagesFromSameOpnMatch(b, c, i, p1_vote_req, p2_vote_req);
}

//////////////////////////////
// APP STATE
//////////////////////////////
lemma {:axiom} lemma_idx_equal (i:int, j:int)
    ensures i == j
// 改个名字
lemma lemma_AppStateAlwaysValid(
    b:Behavior<TpcState>,
    c:Constants,
    i:int,
    idx:int
)
returns
(
    qs:seq<QuorumOfVotes>
)
    requires IsValidBehaviorPrefix(b, c, i)
    requires 0 <= i 
    requires 0 <= idx < |b[i].hosts|
    ensures IsValidQuorumOfVotesSequence(b[i], qs)
    ensures |qs| == b[i].hosts[idx].host.coordinator.opn_complete
    // ensures b[i].hosts[idx].host.participant.app == GetAppStateFromRequests(GetSequenceOfRequest(qs))
    decreases i
{
    if i == 0
    {
        qs := [];
        return;
    }

    lemma_HostConstantsAllConsistent(b, c, i, idx);
    lemma_HostConstantsAllConsistent(b, c, i-1, idx);
    lemma_AssumptionsMakeValidTransition(b, c, i-1);

    var s := b[i-1].hosts[idx].host.coordinator;
    var s' := b[i].hosts[idx].host.coordinator;

    if s'.opn_complete == s.opn_complete
    {
        qs := lemma_AppStateAlwaysValid(b, c, i-1, idx);
        lemma_IfValidQuorumOfVotesSequenceNowThenNext(b, c, i-1, qs);
        return;
    }

    var ios := lemma_ActionThatChangesHostIsThatHostsAction(b, c, i-1, idx);
    assert b[i-1].hosts[idx].nextActionIndex == 2;

    var prev_state := lemma_AppStateAlwaysValid(b, c, i-1, idx);
    lemma_idx_equal(idx, c.params.coor_id);
    assume idx == c.params.coor_id;
    var q := lemma_DecidedOpnWasChosen(b, c, i-1, idx);
    qs := prev_state + [q];
}

lemma lemma_RegularQuorumOfVoteSequenceIsPrefixOfMaximalQuorumOfVoteSequence(
    b:Behavior<TpcState>,
    c:Constants,
    i:int,
    qs_regular:seq<QuorumOfVotes>,
    qs_maximal:seq<QuorumOfVotes>
)
    requires IsValidBehaviorPrefix(b, c, i)
    requires 0 <= i 
    requires IsValidQuorumOfVotesSequence(b[i], qs_regular)
    requires IsMaximalQuorumOfVoteSequence(b[i], qs_maximal)
    ensures |GetSequenceOfRequest(qs_regular)| <= |GetSequenceOfRequest(qs_maximal)|
    ensures GetSequenceOfRequest(qs_regular) == GetSequenceOfRequest(qs_maximal)[..|GetSequenceOfRequest(qs_regular)|]
{
    var reqs1 := GetSequenceOfRequest(qs_regular);
    var reqs2 := GetSequenceOfRequest(qs_maximal);

    if |qs_regular| > |qs_maximal|
    {
        assert IsValidQuorumOfVotes(b[i], qs_regular[|qs_maximal|]) && qs_regular[|qs_maximal|].opn == |qs_maximal|;
        assert false;
    }

    forall opn | 0 <= opn < |qs_regular|
        ensures reqs1[opn] == reqs2[opn]
    {
        // for each opn, qs_regular and qs_maximal has the same reqeust
        lemma_DecideQuorumsMatchValue(b, c, i, qs_regular[opn], qs_maximal[opn]);
        lemma_SequenceOfRequestsNthElement(qs_regular, opn);
        lemma_SequenceOfRequestsNthElement(qs_maximal, opn);
    }
}

// lemma lemma_ReplyInReplyCacheIsAllowed(
//     server_addresses:set<NodeIdentity>,
//     b:Behavior<TpcState>,
//     c:Constants,
//     i:int,
//     client:NodeIdentity,
//     idx:int
// )
// returns
// (
//     qs:seq<QuorumOfVotes>,
//     reqs:seq<Request>,
//     req_num:int
// )
//     requires IsValidBehaviorPrefix(b, c, i+1)
//     requires |server_addresses| > 0
//     requires 0 <= i 
//     requires 0 <= idx < |c.config.node_ids|
//     requires 0 <= idx < |b[i].hosts|
//     requires client in b[i].hosts[idx].host.participant.reply_cache
//     ensures IsValidQuorumOfVotesSequence(b[i], qs)
//     ensures reqs == GetSequenceOfRequest(qs)
//     ensures 0 <= req_num < |reqs|
//     ensures b[i].hosts[idx].host.participant.reply_cache[client] == GetReplyFromRequests_distributed(server_addresses, reqs, req_num)
// {
//     if i == 0
//     {
//         return;
//     }

//     lemma_ConstantsAllConsistent(b, c, i-1);
//     lemma_ConstantsAllConsistent(b, c, i);
//     lemma_AssumptionsMakeValidTransition(b, c, i-1);

//     var s := b[i-1].hosts[idx].host.participant;
//     var s' := b[i].hosts[idx].host.participant;
//     if client in s.reply_cache && s'.reply_cache[client] == s.reply_cache[client]
//     {
//         qs, reqs, req_num := lemma_ReplyInReplyCacheIsAllowed(server_addresses, b, c, i-1, client, idx);
//         return;
//     }

//     var ios := lemma_ActionThatChangesReplicaIsThatReplicasAction(b, c, i-1, idx);
//     var nextActionIndex := b[i-1].hosts[idx].nextActionIndex;
//     // if nextActionIndex == 0
//     // {
//     //     var p := ios[0].r;
//     //     qs, reqs, req_num := 
//     // }

//     assert nextActionIndex == 0;

//     var qs_prev := lemma_AppStateAlwaysValid(b, c, i-1, idx);
    
// }


// 之后可能要改
predicate VotesAreTheSame(v1:seq<int>, v2:seq<int>)
{
    v1 == v2
}

// lemma lemma_QuorumOfVotesStayValid(
//     b:Behavior<TpcState>,
//     c:Constants,
//     i:int,
//     j:int,
//     q:QuorumOfVotes
// )
//     requires IsValidBehaviorPrefix(b, c, j)
//     requires IsValidQuorumOfVotes(b[i], q)
//     requires 0 <= i <= j
//     ensures IsValidQuorumOfVotes(b[j], q)
// {

// }

lemma lemma_A(s:set<int>, a:int, b:int)
    requires forall i :: i in s ==> 0 <= i < a 
    requires a == b 
    ensures forall i :: i in s ==> 0 <= i < b

lemma lemma_B(c:Constants, packets1:seq<TpcPacket>, packets2:seq<TpcPacket>, coor:Coordinator, opn:int)
    requires |packets1| == |c.config.node_ids|
    requires |packets2| == |c.config.node_ids|
    requires opn in coor.request_states
    requires forall i :: i in c.config.node_ids ==> i in coor.request_states[opn].votes
    requires forall i :: 0 <= i < |c.config.node_ids| ==>
                var p1 := packets1[i];
                var p2 := packets2[i];
                var sender := c.config.node_ids[i];
                && p1 == coor.request_states[opn].votes[sender]
                && p2 == coor.request_states[opn].votes[sender]
                // && p1 == p2
    ensures packets1 == packets2

lemma {:axiom} lemma_C(c:Constants, packets1:seq<TpcPacket>, coor:Coordinator, opn:int)
    requires |packets1| == |c.config.node_ids|
    requires opn in coor.request_states
    requires forall i :: i in c.config.node_ids ==> i in coor.request_states[opn].votes
    ensures forall i :: 0 <= i < |c.config.node_ids| ==>
                var p1 := packets1[i];
                var sender := c.config.node_ids[i];
                && p1 == coor.request_states[opn].votes[sender]

lemma {:axiom} lemma_D(packets1:seq<TpcPacket>, packets2:seq<TpcPacket>)
    ensures packets1 == packets2

// 找到判断opn可以被CoordinatorGetDecision时候的quorum
// s是CoordinatorGetDecision之前，s'是CoordinatorGetDecision之后
lemma lemma_DecidedOpnWasChosen(
    b:Behavior<TpcState>,
    c:Constants,
    i:int,
    idx:int
)
returns
(
    q:QuorumOfVotes
)
    requires IsValidBehaviorPrefix(b, c, i)
    requires 0 <= i 
    requires 0 <= idx < |b[i].hosts|
    requires b[i].hosts[idx].host.coordinator.next_op_to_be_decided.OperationToBeDecided?
    requires idx == c.params.coor_id
    ensures IsValidQuorumOfVotes(b[i], q)
    ensures var s := b[i].hosts[idx].host.coordinator;
            var votes := ConvertVotePacketsToVoteSeqs(q.packets);
            && q.opn == s.opn_complete 
            && q.v == s.next_op_to_be_decided.v 
            && votes == s.next_op_to_be_decided.votes
            && (forall v :: v in votes ==> v == ParticipantMakeVote(q.v.req))
{
    if i == 0 
    {
        return;
    }

    lemma_HostConstantsAllConsistent(b, c, i, idx);
    lemma_HostConstantsAllConsistent(b, c, i-1, idx);
    lemma_AssumptionsMakeValidTransition(b, c, i-1);

    var s := b[i-1].hosts[idx].host;
    var s' := b[i].hosts[idx].host;
    // 应该是next_op_to_be_decide 和 opn_complete 没有同步更新
    assert s.coordinator.opn_complete == s'.coordinator.opn_complete;

    if s'.coordinator.next_op_to_be_decided == s.coordinator.next_op_to_be_decided
    {
        q := lemma_DecidedOpnWasChosen(b, c, i-1, idx);
        // lemma_QuorumOfVotesStayValid(b, c, i-1, i, q);
        // assert q.v == s.coordinator.next_op_to_be_decided.v;
        assert q.opn == s.coordinator.opn_complete;
        // assert q.v == s'.coordinator.next_op_to_be_decided.v;
        assert q.opn == s'.coordinator.opn_complete;
        return;
    }

    var ios := lemma_ActionThatChangesHostIsThatHostsAction(b, c, i-1, idx);
    assert b[i-1].hosts[idx].nextActionIndex == 1;
    var opn := s.coordinator.opn_complete;
    var votes_packets := s.coordinator.request_states[opn].votes;
    var req := s.coordinator.request_states[opn].req;
    
    assert opn in s.coordinator.request_states;
    assert ReceivedAllVotes(s.coordinator.constants.all.config.node_ids, votes_packets);
    assert |votes_packets| == |s.coordinator.constants.all.config.node_ids|;
    assert |votes_packets| == |c.config.node_ids|;
    var votepackets := ConvertVotePacketMapToVotePacketSequence(s.coordinator.constants.all.config.node_ids, votes_packets);
    var votes := ConvertVotePacketsToVoteSeqs(votepackets);
    assert s'.coordinator.next_op_to_be_decided == OperationToBeDecided(req, votes);
    assert votes == s'.coordinator.next_op_to_be_decided.votes;
    var senders := set i | i in s.coordinator.request_states[opn].votes;
    // assert |senders| == |votes_packets|;

    
    var indices:set<int> := {};
    var packets:seq<TpcPacket> := [];
    var sender_idx := 0;
    var dummy_packet := LPacket(c.config.node_ids[0], c.config.node_ids[0], VoteReqMsg(opn, idx, req));

    while sender_idx < |c.config.node_ids|
        invariant 0 <= sender_idx <= |c.config.node_ids|
        invariant |packets| == sender_idx
        invariant |indices| == sender_idx
        invariant forall sidx :: sidx in indices ==> && 0 <= sidx < sender_idx
                                                    && var p := packets[sidx];
                                                    && var sender := c.config.node_ids[sidx];
                                                    && p == s.coordinator.request_states[opn].votes[sender]
                                                    && p.src == b[i].constants.config.node_ids[sidx]
                                                    && p.msg.VoteMsg?
                                                    && p.msg.opn_vote == opn
                                                    && p.msg.request == req
                                                    && p.msg.coor_id == idx
                                                    && p.msg.vote == ParticipantMakeVote(req.req)
                                                    && p in b[i].environment.sentPackets
        invariant forall sidx :: 0 <= sidx < sender_idx && c.config.node_ids[sidx] in senders ==> sidx in indices
    {
        var sender := c.config.node_ids[sender_idx];
        // if sender in senders {
            var sender_idx_unused, p := lemma_GetSentVoteMessageFromRequestStates(b, c, i, idx, opn, sender);
            assert NodesDistinct(c.config.node_ids, sender_idx, GetNodeIndex(p.src, c.config));
            assert p == s.coordinator.request_states[opn].votes[sender];
            packets := packets + [p];
            indices := indices + {sender_idx};
        // }
        // else
        // {
        //     packets := packets + [dummy_packet];
        // }
        sender_idx := sender_idx + 1;
    }


    assert |votepackets| == |c.config.node_ids|;
    assert opn in s.coordinator.request_states;
    assert forall i :: i in c.config.node_ids ==> i in s.coordinator.request_states[opn].votes;
    // lemma_C(c, votepackets, s.coordinator, opn);
    // assume forall i :: 0 <= i < |c.config.node_ids| ==> var p := votepackets[i]; var sender := c.config.node_ids[i];
    //                                                     p == s.coordinator.request_states[opn].votes[sender];
    assert |packets| == |c.config.node_ids|;
    assert forall i :: 0 <= i < |c.config.node_ids| ==> var p := packets[i]; var sender := c.config.node_ids[i];
                                                        p == s.coordinator.request_states[opn].votes[sender];
    // lemma_B(c, packets, votepackets, s.coordinator, opn);
    // assert forall i :: i <= i < |c.config.node_ids| ==> packets[i] == votepackets[i];
    lemma_D(packets, votepackets);
    assert packets == votepackets;

    assert forall i :: i in indices ==> 0 <= i < sender_idx;
    assert sender_idx == |c.config.node_ids|;
    assert forall i :: i in indices ==> 0 <= i < |c.config.node_ids|;
    assert c.config == b[i].constants.config;
    assert |c.config.node_ids| == |b[i].constants.config.node_ids|;
    lemma_A(indices, |c.config.node_ids|, |b[i].constants.config.node_ids|);
    // assert forall i :: i in indices ==> 0 <= i < |b[i].constants.config.node_ids|;
    

    // assert |indices| == |c.config.node_ids|;

    lemma_ReceivedVoteMessageSenderAlwaysValidHosts(b, c, i-1, idx, opn);
    var alt_indices := lemma_GetIndicesFromNodes(senders, c.config);
    forall sidx | sidx in alt_indices
        ensures sidx in indices
    {
        assert 0 <= sidx < |c.config.node_ids|;
        assert c.config.node_ids[sidx] in senders;
    }
    SubsetCardinality(alt_indices, indices);

    assert |indices| == |c.config.node_ids|;
    assert |indices| == |b[i].constants.config.node_ids|;
    // assert forall i :: i in indices ==> 0 <= i < |b[i].constants.config.node_ids|;
    assert |packets| == |c.config.node_ids|;
    
    assert forall p :: p in packets ==> p.msg.VoteMsg?;
    assert forall p :: p in packets ==> p.msg.vote == ParticipantMakeVote(req.req);
    var vote_seq := ConvertVotePacketsToVoteSeqs(packets);
    assert vote_seq == s'.coordinator.next_op_to_be_decided.votes;
    assert forall v :: v in vote_seq ==> v == ParticipantMakeVote(req.req);
    
    q := QuorumOfVotes(c, indices, packets, idx, opn, req.tid, req);
    // assert |q.indices| == |b[i].constants.config.node_ids|;
    // assert |q.indices| > 0;
    // assert |q.packets| == |b[i].constants.config.node_ids|;
    // assert q.v.tid == q.tid;
    // assert q.c == b[i].constants;
    // assert q.coor == q.c.params.coor_id;
    // assert forall idx1 :: idx1 in q.indices ==> && 0 <= idx1 < |b[i].constants.config.node_ids|
    //                                     && var p := q.packets[idx1];
    //                                     && p.src == b[i].constants.config.node_ids[idx1]
    //                                     && p.msg.VoteMsg?
    //                                     && p.msg.opn_vote == q.opn
    //                                     && p.msg.request == q.v
    //                                     && p.msg.coor_id == q.coor
    //                                     && p in b[i].environment.sentPackets;
    // assert QuorumOfVotesAllVoteMsgs(q);
}

// 找到通过coordinator replytoclient 发出的reply对应的qs
lemma lemma_ReplySentViaCoordinatorMakeDecisionIsAllowed(
    server_addresses:set<NodeIdentity>,
    b:Behavior<TpcState>,
    c:Constants,
    i:int,
    p:TpcPacket,
    idx:int,
    ios:seq<TpcIo>
)
returns
(
    qs:seq<QuorumOfVotes>,
    reqs:seq<Request>,
    req_num:int
)
    requires IsValidBehaviorPrefix(b, c, i+1)
    requires |server_addresses| > 0
    requires 0 <= i
    requires 0 <= idx < |c.config.node_ids|
    requires 0 <= idx < |b[i].hosts|
    requires idx == c.params.coor_id
    requires LIoOpSend(p) in ios
    requires TpcNext(b[i], b[i+1])
    requires b[i].environment.nextStep == LEnvStepHostIos(c.config.node_ids[idx], ios)
    requires b[i].hosts[idx].host.coordinator.next_op_to_be_decided.OperationToBeDecided?
    requires b[i].hosts[idx].host.coordinator.opn_complete in b[i].hosts[idx].host.coordinator.request_states
    requires HostConstantsValid(b[i].hosts[idx].host.coordinator.constants)
    requires CoordinatorMakeDecision(b[i].hosts[idx].host.coordinator, 
                                            b[i+1].hosts[idx].host.coordinator,
                                            ExtractSentPacketsFromIos(ios))
    // requires CoordinatorMaybeMakeDecision(b[i].hosts[idx].host.coordinator, 
    //                                         b[i+1].hosts[idx].host.coordinator,
    //                                         ExtractSentPacketsFromIos(ios))
    ensures IsValidQuorumOfVotesSequence(b[i], qs)
    ensures reqs == GetSequenceOfRequest(qs)
    ensures 0 <= req_num < |reqs|
    ensures Reply(p.dst, p.msg.tid, p.msg.reply) == GetReplyFromRequests_distributed(server_addresses, reqs, req_num)
{
    lemma_HostConstantsAllConsistent(b, c, i, idx);
    lemma_HostConstantsAllConsistent(b, c, i+1, idx);
    // assert 0 <= idx < |b[i].hosts|;
    // assert 0 <= idx < |b[i-1].hosts|;

    // var coor := b[i].hosts[idx].host.coordinator;
    // var opn_complete := coor.opn_complete;
    // assert opn_complete >= 0;
    // qs := lemma_GetMaximalQuorumOfVotesSequenceWithinBound(b, c, i, opn_complete);
    // // assert 
    // assert |qs| > 0;
    // reqs := GetSequenceOfRequest(qs);
    // req_num := |reqs|-1;
    
    // var prev_state;
    // if |qs| > 0 {
    //     prev_state := GetAppStateFromRequests(reqs[..req_num]);
    // }
    // else
    // {
    //     prev_state := AppInitialize();
    // }

    var coor := b[i].hosts[idx].host.coordinator;
    var opn_complete := coor.opn_complete;
    // var qs_prev;
    // if opn_complete >= 1 
    // {
    //     qs_prev := lemma_GetMaximalQuorumOfVotesSequenceWithinBound(b, c, i, opn_complete - 1);
    // }
    // else 
    // {
    //     qs_prev := [];
    // }

    // assert opn_complete > 1;
    // var qs_prev := lemma_GetMaximalQuorumOfVotesSequenceWithinBound(b, c, i, opn_complete - 1);

    var qs_prev := lemma_AppStateAlwaysValid(b, c, i, idx);
    
   
    var q := lemma_DecidedOpnWasChosen(b, c, i, idx);
    var req := q.v;

    qs := qs_prev + [q];
    reqs := GetSequenceOfRequest(qs);
    req_num := |qs_prev|;
    assert qs[req_num] == q;
    assert req_num == coor.opn_complete;


    // var req := reqs[req_num];
    
    // votes1是模拟分布式执行得到的投票
    var votes1 := HandleRequestInDistributedWay(server_addresses, req.req);
    
    assert forall v :: v in votes1 ==> v == ParticipantMakeVote(req.req);
    var decision1 := CoorMakeDecision(votes1);
    var reply1 := CoordinatorGenerateReply(req, decision1);
    assert reply1 == GetReplyFromRequests_distributed(server_addresses, reqs, req_num);

    // // var q := last(qs);
    // // var votes_packets := q.packets;
    // // 按照coordinatormakedeicision逻辑得到reply
    // var req2 := coor.request_states[opn_complete].req;
    // assert req2 == req;
    // var votes_packets := coor.request_states[opn_complete].votes;
    // // assert forall p :: p in votes_packets ==> votes_packets[p] == ParticipantMakeVote(req2.req);
    // var votes2 := ConvertVotesToVoteSequence(coor.constants.all.config.node_ids, votes_packets);
    // assert forall v :: v in votes2 ==> v == ParticipantMakeVote(req2.req);
    // assert req == req2;
    // assert forall v :: v in votes2 ==> v == ParticipantMakeVote(req.req);
    // // assert votes1 == votes2;
    // var decision2 := CoorMakeDecision(votes2);
    // var reply2 := CoordinatorGenerateReply(req2, decision2);
    // var me := c.config.node_ids[idx];
    // var reply_packet := LPacket(req.client, me, ReplyMsg(reply2.tid, reply2.rep));
    // assert p == reply_packet;

    // votes2是coordinator收集到的真实投票
    var req2 := coor.next_op_to_be_decided.v;
    var votes2 := coor.next_op_to_be_decided.votes;
    assert forall v :: v in votes2 ==> v == ParticipantMakeVote(req2.req);
    assert forall v :: v in votes2 ==> v == ParticipantMakeVote(req.req);
    assert forall v :: v in votes1 ==> v == ParticipantMakeVote(req.req);
    assert forall v :: v in votes1 ==> v == ParticipantMakeVote(req2.req);
    assert |votes2| == |coor.constants.all.config.node_ids|;
    // assert |votes2| == |votes1|;
    // assert forall v :: v in votes1 ==> exists i :: i in votes2 && v == i;

    lemma_votes_are_same(votes1, votes2);
    assert forall v :: v in votes1 ==> v in votes2;
    assert forall v :: v in votes2 ==> v in votes1;
    var decision2 := CoorMakeDecision(votes2);
    var reply2 := CoordinatorGenerateReply(req2, decision2);

    // assert votes1 == votes2;
    assert req == req2;
    assert decision1 == decision2;
    assert reply1 == reply2;

    // var q := lemma_DecidedOpnWasChosen(b, c, i, idx);
    // qs := qs_prev + [q];
    // reqs := GetSequenceOfRequest(qs);
    // req_num := |qs_prev|;

    // assert GetSequenceOfRequest(qs_prev) == reqs[..req_num];

    // var s := b[i].hosts[idx].host.coordinator;
    // assert s.app == GetAppStateFromRequests(GetSequenceOfRequest(qs_prev));
}

lemma {:axiom} lemma_votes_are_same(v1:seq<int>, v2:seq<int>)
    ensures forall v :: v in v1 ==> v in v2

// for a reply, there exists a request can procude the same reply
// find the qs and req_num that can produce the same reply
lemma lemma_ReplySentIsAllowed(
    server_addresses:set<NodeIdentity>,
    b:Behavior<TpcState>,
    c:Constants,
    i:int,
    p:TpcPacket
)
returns
(
    qs:seq<QuorumOfVotes>,
    reqs:seq<Request>,
    req_num:int
)
    requires IsValidBehaviorPrefix(b, c, i)
    requires |server_addresses| > 0
    requires 0 <= i 
    requires p in b[i].environment.sentPackets
    requires p.src in c.config.node_ids
    requires p.msg.ReplyMsg?
    ensures IsValidQuorumOfVotesSequence(b[i], qs)
    ensures reqs == GetSequenceOfRequest(qs)
    ensures 0 <= req_num < |reqs|
    ensures Reply(p.dst, p.msg.tid, p.msg.reply) == GetReplyFromRequests_distributed(server_addresses, reqs, req_num)
    decreases i
{
    if i == 0 
    {
        return;
    }

    lemma_ConstantsAllConsistent(b, c, i-1);
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_AssumptionsMakeValidTransition(b, c, i-1);

    // assert TpcNext(b[i-1], b[i]);
    // assert (exists idx, ios :: TpcNextOneHost(b[i-1], b[i], idx, ios)) || (exists eid, ios :: TpcNextOneExternal(b[i-1], b[i], eid, ios)) || TpcNextEnvironment(b[i-1], b[i]);

    // assert p in b[i].environment.sentPackets;
    // assert p in b[i-1].environment.sentPackets;

    if p in b[i-1].environment.sentPackets
    {
        qs, reqs, req_num := lemma_ReplySentIsAllowed(server_addresses, b, c, i-1, p);
        lemma_IfValidQuorumOfVotesSequenceNowThenNext(b, c, i-1, qs);
        return;
    }

    assert b[i-1].environment.nextStep.LEnvStepHostIos?;
    assert LIoOpSend(p) in b[i-1].environment.nextStep.ios;
    var idx := GetNodeIndex(b[i-1].environment.nextStep.actor, c.config);
    // assert b[i-1].hosts[idx].host.constants.
    lemma_idx_equal(idx, c.params.coor_id);
    assume idx == c.params.coor_id;
    var ios := b[i-1].environment.nextStep.ios;
    var idx_alt :| TpcNextOneHost(b[i-1], b[i], idx_alt, ios);
    assert NodesDistinct(c.config.node_ids, idx, idx_alt);

    var nextActionIndex := b[i-1].hosts[idx].nextActionIndex;
    // if nextActionIndex == 0
    // {
    //     qs, reqs, req_num := lemma_ReplyInReplyCacheIsAllowed(server_addresses, b, c, i-1, ios[0].r.src, idx);
    //     lemma_IfValidQuorumOfVotesSequenceNowThenNext(b, c, i-1, qs);
    //     assert b[i].hosts[idx].host.participant.reply_cache[ios[0].r.src] == GetReplyFromRequests_distributed(server_addresses, reqs, req_num);
    //     assert b[i].hosts[idx].host.participant.reply_cache[ios[0].r.src] == Reply(p.dst, p.msg.tid, p.msg.reply);
    //     assert Reply(p.dst, p.msg.tid, p.msg.reply) == GetReplyFromRequests_distributed(server_addresses, reqs, req_num);
    // }
    // else 
    if nextActionIndex == 2
    {
        qs, reqs, req_num := lemma_ReplySentViaCoordinatorMakeDecisionIsAllowed(server_addresses, b, c, i-1, p, idx, ios);
        lemma_IfValidQuorumOfVotesSequenceNowThenNext(b, c, i-1, qs);
        assert Reply(p.dst, p.msg.tid, p.msg.reply) == GetReplyFromRequests_distributed(server_addresses, reqs, req_num);
    }
    else
    {
        assert false;
    }
}

}