include "../DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Constants.i.dfy"
include "Environment.i.dfy"
include "Actions.i.dfy"
include "PacketSending.i.dfy"

module TpcRefinement__MessageVoteRequest_i {
import opened LiveTPC__DistributedSystem_i
import opened LiveTPC__Constants_i
import opened LiveTPC__Message_i
import opened LiveTPC__Configuration_i
import opened TpcRefinement__Assumptions_i
import opened TpcRefinement__Constants_i
import opened TpcRefinement__Environment_i
import opened TpcRefinement__Actions_i
import opened TpcRefinement__PacketSending_i
import opened Temporal__Temporal_s
import opened Environment_s

lemma {:axiom} lemma_idx_equal (i:int, j:int)
    ensures i == j

lemma lemma_VoteReqMessageImplicationsForCoordinatorState(
    b:Behavior<TpcState>,
    c:Constants,
    i:int,
    p:TpcPacket
)
returns
(
    coor_idx:int
)
    requires IsValidBehaviorPrefix(b,c,i)
    requires 0 <= i 
    requires p in b[i].environment.sentPackets
    requires p.src in c.config.node_ids
    requires p.msg.VoteReqMsg?
    ensures 0 <= coor_idx < |c.config.node_ids|
    ensures 0 <= coor_idx < |b[i].hosts|
    ensures p.src == c.config.node_ids[coor_idx]
    ensures p.msg.coor_id == coor_idx
    ensures var s := b[i].hosts[coor_idx].host.coordinator;
            s.next_opn > p.msg.opn_votereq
{
    if i == 0 
    {
        return;
    }

    lemma_AssumptionsMakeValidTransition(b, c, i-1);
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_ConstantsAllConsistent(b, c, i-1);

    if p in b[i-1].environment.sentPackets
    {
        coor_idx := lemma_VoteReqMessageImplicationsForCoordinatorState(b, c, i-1, p);
        var s := b[i-1].hosts[coor_idx].host.coordinator;
        var s' := b[i].hosts[coor_idx].host.coordinator;
        if s' != s 
        {
            var ios := lemma_ActionThatChangesHostIsThatHostsAction(b, c, i-1, coor_idx);
        }
        return;
    }
    
    var ios:seq<TpcIo>;
    coor_idx, ios := lemma_ActionThatSendsVoteReqIsProcessRequest(b[i-1], b[i], p);
}

// lemma lemma_SentVoteReqMessageImpliesOpnInRequestStates(
//     ps:TpcState,
//     ps':TpcState,
//     idx:int,
//     p:TpcPacket
// )
//     requires p.src in ps.constants.config.node_ids
//     requires p.msg.VoteReqMsg?
//     requires p in ps'.environment.sentPackets
//     requires p in ps.environment.sentPackets
//     requires TpcNext(ps, ps')
//     requires 0 <= idx < |ps'.constants.config.node_ids|
//     requires p.msg.opn_votereq in ps'.hosts[idx].host.coordinator.request_states
//     ensures p.msg.opn_votereq in ps.hosts[idx].host.coordinator.request_states
//     ensures ps.hosts[idx].host.coordinator.request_states[p.msg.opn_votereq].req == ps'.hosts[idx].host.coordinator.request_states[p.msg.opn_votereq].req
// {
//     // assert ps.environment.nextStep.LEnvStepHostIos?;
//     // assert LIoOpSend(p) in ps.environment.nextStep.ios;
//     // var idx, ios :| TpcNextOneHost(ps, ps', idx, ios) && LIoOpSend(p) in ios;
//     if ps.hosts[idx] == ps'.hosts[idx]
//     {
//         assert p.msg.opn_votereq in ps.hosts[idx].host.coordinator.request_states;
//         assert ps.hosts[idx].host.coordinator.request_states[p.msg.opn_votereq].req == ps'.hosts[idx].host.coordinator.request_states[p.msg.opn_votereq].req;
//         return;
//     }
//     else if ps.hosts[idx].nextActionIndex > 0
//     {
//         assert p.msg.opn_votereq in ps.hosts[idx].host.coordinator.request_states;
//         assert ps.hosts[idx].host.coordinator.request_states[p.msg.opn_votereq].req == ps'.hosts[idx].host.coordinator.request_states[p.msg.opn_votereq].req;
//         return;
//     }
//     else
//     {
        
//     }
// }



lemma lemma_SentVoteReqMessageImpliesOpnInRequestStates(
    b:Behavior<TpcState>,
    c:Constants,
    ps:TpcState,
    ps':TpcState,
    i:int,
    idx:int,
    p:TpcPacket
)
    requires IsValidBehaviorPrefix(b, c, i)
    requires 0 <= i 
    requires ps' == b[i]
    requires ps == b[i-1]
    requires p.src in ps.constants.config.node_ids
    requires p.msg.VoteReqMsg?
    requires p in ps'.environment.sentPackets
    requires p in ps.environment.sentPackets
    requires TpcNext(ps, ps')
    requires 0 <= idx < |ps'.constants.config.node_ids|
    requires p.msg.opn_votereq in ps'.hosts[idx].host.coordinator.request_states
    ensures p.msg.opn_votereq in ps.hosts[idx].host.coordinator.request_states
    ensures ps.hosts[idx].host.coordinator.request_states[p.msg.opn_votereq].req == ps'.hosts[idx].host.coordinator.request_states[p.msg.opn_votereq].req
{
    // assert ps.environment.nextStep.LEnvStepHostIos?;
    // assert LIoOpSend(p) in ps.environment.nextStep.ios;
    // var idx, ios :| TpcNextOneHost(ps, ps', idx, ios) && LIoOpSend(p) in ios;
    if ps.hosts[idx] == ps'.hosts[idx]
    {
        assert p.msg.opn_votereq in ps.hosts[idx].host.coordinator.request_states;
        assert ps.hosts[idx].host.coordinator.request_states[p.msg.opn_votereq].req == ps'.hosts[idx].host.coordinator.request_states[p.msg.opn_votereq].req;
        return;
    }
    else if ps.hosts[idx].nextActionIndex > 0
    {
        assert p.msg.opn_votereq in ps.hosts[idx].host.coordinator.request_states;
        assert ps.hosts[idx].host.coordinator.request_states[p.msg.opn_votereq].req == ps'.hosts[idx].host.coordinator.request_states[p.msg.opn_votereq].req;
        return;
    }

    assert ps.hosts[idx].nextActionIndex == 0;
    var s := ps.hosts[idx].host.coordinator;
    var s' := ps'.hosts[idx].host.coordinator;

    var ios := lemma_ActionThatChangesHostIsThatHostsAction(b, c, i-1, idx);
    assert |ios| > 0;
    if ios[0].LIoOpTimeoutReceive?
    {
        return;
    }
    assert ios[0].LIoOpReceive?;
    var packet_receive := ios[0].r;

    if !packet_receive.msg.RequestMsg?
    {
        return;
    }
    else
    {
        lemma_AssumptionsMakeValidTransition(b, c, i-2);
        lemma_ConstantsAllConsistent(b, c, i-1);
        lemma_ConstantsAllConsistent(b, c, i-2);

        // if p in b[i-2].environment.sentPackets
        // {
        //     lemma_SentVoteReqMessageImpliesOpnInRequestStates(b, c, b[i-2], b[i-1], i-1, idx, p);
        //     return;
        // }
        lemma_SentVoteReqMessageImpliesNextOpnIsLarger(b, c, i-1, idx, p);
        assert packet_receive.msg.RequestMsg?;
        var opn := s.next_opn;
        assert opn > p.msg.opn_votereq;
        // assert opn != p.msg.opn_votereq;
    }

    // else if 
    // {
    //     var ios := lemma_ActionThatChangesHostIsThatHostsAction(b, c, i-1, idx);
    // }
}

lemma lemma_SentVoteReqMessageImpliesNextOpnIsLarger(
    b:Behavior<TpcState>,
    c:Constants,
    i:int,
    idx:int,
    p:TpcPacket
)
    requires IsValidBehaviorPrefix(b, c, i)
    requires 0 <= i 
    requires p in b[i].environment.sentPackets
    requires p.src in c.config.node_ids
    requires p.msg.VoteReqMsg?
    requires 0 <= idx < |b[i].hosts|
    // requires p.msg.opn_votereq in b[i].hosts[idx].host.coordinator.request_states
    ensures p.msg.opn_votereq < b[i].hosts[idx].host.coordinator.next_opn
{
    if i == 0 
    {
        return;
    }

    lemma_AssumptionsMakeValidTransition(b, c, i-1);
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_ConstantsAllConsistent(b, c, i-1);

    if p in b[i-1].environment.sentPackets
    {
        lemma_SentVoteReqMessageImpliesNextOpnIsLarger(b, c, i-1, idx, p);
        return;
    }
    else
    {
        var idx1, ios := lemma_ActionThatSendsVoteReqIsProcessRequest(b[i-1], b[i], p);
        lemma_idx_equal(idx1, idx);
        assume idx1 == idx;
        assert p.msg.opn_votereq < b[i].hosts[idx].host.coordinator.next_opn;
    }
}

lemma lemma_VoteReqMessageIsSentByProcessRequest(
    b:Behavior<TpcState>,
    c:Constants,
    i:int,
    idx:int,
    p:TpcPacket
)
    requires IsValidBehaviorPrefix(b, c, i)
    requires 0 <= i 
    requires p in b[i].environment.sentPackets
    requires p.src in c.config.node_ids
    requires p.msg.VoteReqMsg?
    requires 0 <= idx < |b[i].hosts|
    requires p.msg.opn_votereq in b[i].hosts[idx].host.coordinator.request_states
    ensures p.msg.request == b[i].hosts[idx].host.coordinator.request_states[p.msg.opn_votereq].req
{
    if i == 0 
    {
        return;
    }

    lemma_AssumptionsMakeValidTransition(b, c, i-1);
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_ConstantsAllConsistent(b, c, i-1);

    if p in b[i-1].environment.sentPackets
    {
        lemma_SentVoteReqMessageImpliesOpnInRequestStates(b, c, b[i-1], b[i], i, idx, p);
        // assert p.msg.opn_votereq in b[i-1].hosts[idx].host.coordinator.request_states;
        lemma_VoteReqMessageIsSentByProcessRequest(b, c, i-1, idx, p);
        assert p.msg.opn_votereq in b[i-1].hosts[idx].host.coordinator.request_states;
        assert p.msg.request == b[i-1].hosts[idx].host.coordinator.request_states[p.msg.opn_votereq].req;
        // assert b[i].hosts[idx].host.coordinator.request_states[p.msg.opn_votereq].req == b[i-1].hosts[idx].host.coordinator.request_states[p.msg.opn_votereq].req;
        assert p.msg.opn_votereq in b[i].hosts[idx].host.coordinator.request_states;
        assert b[i].hosts[idx].host.coordinator.request_states[p.msg.opn_votereq].req == b[i-1].hosts[idx].host.coordinator.request_states[p.msg.opn_votereq].req;
        assert p.msg.request == b[i].hosts[idx].host.coordinator.request_states[p.msg.opn_votereq].req;
        return;
    }
    else
    {
        // assert b[i].hosts[idx].nextActionIndex == 0;
        var idx1, ios := lemma_ActionThatSendsVoteReqIsProcessRequest(b[i-1], b[i], p);
        assert p.msg.opn_votereq in b[i].hosts[idx].host.coordinator.request_states;
        lemma_idx_equal(idx, idx1);
        assume idx == idx1;
        assert p.msg.request == b[i].hosts[idx1].host.coordinator.request_states[p.msg.opn_votereq].req;
        // assert p.msg.request == b[i].hosts[idx].host.coordinator.request_states[p.msg.opn_votereq].req;
    }
}

lemma lemma_VoteReqMessagesFromSameOpnMatchWithoutLossOfGenerality(
    b:Behavior<TpcState>,
    c:Constants,
    i:int,
    p1:TpcPacket,
    p2:TpcPacket
)
    requires IsValidBehaviorPrefix(b, c, i)
    requires 0 <= i 
    requires p1 in b[i].environment.sentPackets
    requires p2 in b[i].environment.sentPackets
    requires p1.src in c.config.node_ids
    requires p2.src in c.config.node_ids
    requires p1.msg.VoteReqMsg?
    requires p2.msg.VoteReqMsg?
    requires p1.msg.opn_votereq == p2.msg.opn_votereq
    requires p1.msg.coor_id == p2.msg.coor_id
    requires p2 in b[i-1].environment.sentPackets ==> p1 in b[i-1].environment.sentPackets
    ensures p1.msg.request == p2.msg.request
    decreases 2*i
{
    lemma_AssumptionsMakeValidTransition(b, c, i-1);
    lemma_ConstantsAllConsistent(b, c, i);
    lemma_ConstantsAllConsistent(b, c, i-1);

    if p2 in b[i-1].environment.sentPackets
    {
        lemma_VoteReqMessagesFromSameOpnMatch(b, c, i-1, p1, p2);
        return;
    }

    var coor_idx, ios := lemma_ActionThatSendsVoteReqIsProcessRequest(b[i-1], b[i], p2);

    if p1 !in b[i-1].environment.sentPackets
    {
        assert LIoOpSend(p1) in ios;
        assert LIoOpSend(p2) in ios;
        return;
    }

    var alt_coor_idx := lemma_VoteReqMessageImplicationsForCoordinatorState(b, c, i-1, p1);

    var alt2_coor_idx := lemma_VoteReqMessageImplicationsForCoordinatorState(b, c, i, p2);

    assert alt_coor_idx == alt2_coor_idx;
    assert NodesDistinct(c.config.node_ids, coor_idx, alt_coor_idx);
    assert coor_idx == alt_coor_idx;
    assert false;
}

lemma lemma_VoteReqMessagesFromSameOpnMatch(
    b:Behavior<TpcState>,
    c:Constants,
    i:int,
    p1:TpcPacket,
    p2:TpcPacket
)
    requires IsValidBehaviorPrefix(b, c, i)
    requires 0 <= i 
    requires p1 in b[i].environment.sentPackets
    requires p2 in b[i].environment.sentPackets
    requires p1.src in c.config.node_ids
    requires p2.src in c.config.node_ids
    requires p1.msg.VoteReqMsg?
    requires p2.msg.VoteReqMsg?
    requires p1.msg.opn_votereq == p2.msg.opn_votereq
    requires p1.msg.coor_id == p2.msg.coor_id
    ensures p1.msg.request == p2.msg.request
    decreases 2*i+1
{
    if i == 0
    {
        return;
    }

    if p2 in b[i-1].environment.sentPackets && p1 !in b[i-1].environment.sentPackets
    {
        lemma_VoteReqMessagesFromSameOpnMatchWithoutLossOfGenerality(b, c, i, p2, p1);
    }
    else
    {
        lemma_VoteReqMessagesFromSameOpnMatchWithoutLossOfGenerality(b, c, i, p1, p2);
    }
}
}