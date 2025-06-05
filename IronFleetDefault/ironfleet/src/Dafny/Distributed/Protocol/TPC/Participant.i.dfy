include "Constants.i.dfy"
include "Message.i.dfy"
include "../../Common/Collections/Maps.i.dfy"

module LiveTPC__Participant_i {
import opened LiveTPC__Types_i
import opened LiveTPC__Constants_i
import opened LiveTPC__Message_i
import opened AppStateMachine_s
import opened Environment_s
import opened Collections__Maps_i

datatype Participant = Participant(
    constants : HostConstants,
    // app:AppState,
    votefor : map<TxnNumber, int>,
    reply_cache : ReplyCache
)

function ParticipantMakeVote(req:AppRequest) : (int)
{
    var vote := AppHandleRequest(req);
    vote
}

predicate ParticipantInit(p:Participant,c:HostConstants)
{
    && p.constants == c
    // && p.app == AppInitialize()
    && p.votefor == map[]
    && p.reply_cache == map[]
}


predicate ParticipantProcessVoteRequest(s:Participant, s':Participant, packet:TpcPacket, sent_packets:seq<TpcPacket>)
    requires packet.msg.VoteReqMsg?
{
    var opn := packet.msg.opn_votereq;
    if packet.src in s.constants.all.config.node_ids && HostConstantsValid(s.constants) then
        var req := packet.msg.request;
        var tid := req.tid;
        var coor_id := packet.msg.coor_id;
            var vote := ParticipantMakeVote(req.req);
            && s' == s.(votefor := s.votefor[tid := vote])
            && sent_packets == [LPacket(packet.src, s.constants.all.config.node_ids[s.constants.my_index], VoteMsg(opn, coor_id, req, vote))]
    else
        s' == s && sent_packets == []
}

// todo: invoke end transaction when recive the commit decision
predicate ParticipantProcessDecision(s:Participant, s':Participant, packet:TpcPacket, sent_packets:seq<TpcPacket>)
    requires packet.msg.DecisionMsg?
{
    var opn := packet.msg.opn_decision;
    var tid := packet.msg.tid;
    var decision := packet.msg.decision;
    if packet.src in s.constants.all.config.node_ids && tid in s.votefor && HostConstantsValid(s.constants) then
        && s' == s.(votefor := RemoveElt(s.votefor, tid), reply_cache := s.reply_cache[decision.client := decision])
        && sent_packets == []
    else
        s' == s && sent_packets == []
}

}