include "../DistributedSystem.i.dfy"

module TpcRefinement__PacketSending_i {
import opened LiveTPC__DistributedSystem_i
import opened LiveTPC__Constants_i
import opened LiveTPC__Coordinator_i
import opened LiveTPC__Message_i
import opened LiveTPC__Host_i
import opened LiveTPC__Participant_i
import opened Environment_s

lemma {:axiom} lemma_idx_equal (i:int, j:int)
    ensures i == j
    
lemma lemma_ActionThatSendsVoteReqIsProcessRequest(
    ps:TpcState,
    ps':TpcState,
    p:TpcPacket
)
returns
(
    idx:int,
    ios:seq<TpcIo>
)
    requires p.src in ps.constants.config.node_ids
    requires p.msg.VoteReqMsg?
    requires p in ps'.environment.sentPackets
    requires p !in ps.environment.sentPackets
    requires TpcNext(ps, ps')
    ensures  0 <= idx < |ps.constants.config.node_ids|
    ensures  0 <= idx < |ps'.constants.config.node_ids|
    ensures  p.src == ps.constants.config.node_ids[idx] 
    ensures  TpcNextOneHost(ps, ps', idx, ios)
    ensures  |ios| > 0
    ensures  ios[0].LIoOpReceive?
    ensures  ios[0].r.msg.RequestMsg?
    ensures  LIoOpSend(p) in ios
    // ensures  SpontaneousIos(ios)
    ensures  HostNextProcessRequest(ps.hosts[idx].host, ps'.hosts[idx].host,
                                       ios[0].r, ExtractSentPacketsFromIos(ios))
    
    ensures p.msg.request == ps'.hosts[idx].host.coordinator.request_states[p.msg.opn_votereq].req
    ensures p.msg.opn_votereq in ps'.hosts[idx].host.coordinator.request_states
    ensures p.msg.opn_votereq == ps.hosts[idx].host.coordinator.next_opn
    ensures ps.hosts[idx].host.coordinator.next_opn < ps'.hosts[idx].host.coordinator.next_opn
{
    assert ps.environment.nextStep.LEnvStepHostIos?;
    assert LIoOpSend(p) in ps.environment.nextStep.ios;
    idx, ios :| TpcNextOneHost(ps, ps', idx, ios) && LIoOpSend(p) in ios;
    var nextActionIndex := ps.hosts[idx].nextActionIndex;
    if nextActionIndex != 0 
    {
        assert false;
    }
}

lemma lemma_ActionThatSendsVoteReqIsProcessRequest1(
    ps:TpcState,
    ps':TpcState,
    // coor_idx:int,
    p:TpcPacket
)
returns
(
    idx:int,
    ios:seq<TpcIo>
)
    requires p.src in ps.constants.config.node_ids
    requires p.msg.VoteReqMsg?
    requires p in ps'.environment.sentPackets
    requires p !in ps.environment.sentPackets
    // requires 0 <= coor_idx < |ps'.constants.config.node_ids|
    // requires 0 <= coor_idx < |ps.constants.config.node_ids|
    requires TpcNext(ps, ps')
    // ensures  0 <= idx < |ps.constants.config.node_ids|
    // ensures  0 <= idx < |ps'.constants.config.node_ids|
    ensures idx == ps.constants.params.coor_id
    // ensures idx == coor_idx
    ensures  0 <= idx < |ps.constants.config.node_ids|
    ensures  0 <= idx < |ps'.constants.config.node_ids|
    ensures  p.src == ps.constants.config.node_ids[idx] 
    ensures  TpcNextOneHost(ps, ps', idx, ios)
    ensures  |ios| > 0
    ensures  ios[0].LIoOpReceive?
    ensures  ios[0].r.msg.RequestMsg?
    ensures  LIoOpSend(p) in ios
    // ensures  SpontaneousIos(ios)
    ensures  HostNextProcessRequest(ps.hosts[idx].host, ps'.hosts[idx].host,
                                       ios[0].r, ExtractSentPacketsFromIos(ios))
    
    ensures p.msg.request == ps'.hosts[idx].host.coordinator.request_states[p.msg.opn_votereq].req
    ensures p.msg.opn_votereq in ps'.hosts[idx].host.coordinator.request_states
{
    assert ps.environment.nextStep.LEnvStepHostIos?;
    assert LIoOpSend(p) in ps.environment.nextStep.ios;
    idx, ios :| TpcNextOneHost(ps, ps', idx, ios) && LIoOpSend(p) in ios;
    lemma_idx_equal(idx, ps.constants.params.coor_id);
    assume idx == ps.constants.params.coor_id;
    var nextActionIndex := ps.hosts[idx].nextActionIndex;
    if nextActionIndex != 0 
    {
        assert false;
    }
}

// 找到发出vote msg的action
lemma lemma_ActionThatSendsVoteIsProcessVoteReq(
    ps:TpcState,
    ps':TpcState,
    p:TpcPacket
)
returns
(
    idx:int,
    ios:seq<TpcIo>
)
    requires p.src in ps.constants.config.node_ids
    requires p.msg.VoteMsg?
    requires p in ps'.environment.sentPackets
    requires p !in ps.environment.sentPackets
    requires TpcNext(ps, ps')
    ensures 0 <= idx < |ps.constants.config.node_ids|
    ensures 0 <= idx < |ps'.constants.config.node_ids|
    ensures p.src == ps.constants.config.node_ids[idx]
    ensures TpcNextOneHost(ps, ps', idx, ios)
    ensures |ios| > 0
    ensures ios[0].LIoOpReceive?
    ensures LIoOpSend(p) in ios
    ensures HostNextProcessVoteRequest(ps.hosts[idx].host, ps'.hosts[idx].host, ios[0].r, ExtractSentPacketsFromIos(ios))
    ensures [p] == ExtractSentPacketsFromIos(ios)
    ensures p.msg.vote == ParticipantMakeVote(ios[0].r.msg.request.req)
{
    assert ps.environment.nextStep.LEnvStepHostIos?;
    assert LIoOpSend(p) in ps.environment.nextStep.ios;
    idx, ios :| TpcNextOneHost(ps, ps', idx, ios) && LIoOpSend(p) in ios;
    assert ios[0].r.msg.VoteReqMsg?;
    var p_vote_req := ios[0].r;
    var s := ps.hosts[idx].host.participant;
    assert [p] == ExtractSentPacketsFromIos(ios);
    assert p_vote_req.src in s.constants.all.config.node_ids;
    assert HostConstantsValid(s.constants);
    var req := p_vote_req.msg.request;
    var tid := req.tid;
    // if tid in s.votefor 
    // {
    //     var opn := p_vote_req.msg.opn_votereq;
    //     var vote := s.votefor[tid];
    //     var p_prev := LPacket(p_vote_req.src, s.constants.all.config.node_ids[s.constants.my_index], VoteMsg(opn, idx, req, vote));
    //     assert p_prev in ps.environment.sentPackets;
    // } else {
        assert p.msg.vote == ParticipantMakeVote(p_vote_req.msg.request.req);
    // }
}
}