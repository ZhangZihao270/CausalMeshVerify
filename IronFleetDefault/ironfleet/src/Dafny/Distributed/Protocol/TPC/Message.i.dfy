include "Types.i.dfy"
include "../../Common/Framework/Environment.s.dfy"

module LiveTPC__Message_i {
import opened LiveTPC__Types_i
import opened AppStateMachine_s
import opened Environment_s
import opened Concrete_NodeIdentity_i

datatype TpcMessage =
    TpcMessage_Invalid()
  | RequestMsg(tid:TxnNumber, req:AppRequest)
  | VoteReqMsg(opn_votereq:int, coor_id:int, request:Request)
  | VoteMsg(opn_vote:int, coor_id:int, request:Request, vote:int)
  | DecisionMsg(opn_decision:int, tid:TxnNumber, decision:Reply)
  | ReplyMsg(tid:TxnNumber, reply:AppReply)

type TpcPacket = LPacket<NodeIdentity, TpcMessage>
type TpcIo = LIoOp<NodeIdentity, TpcMessage>
type TpcEnvironment = LEnvironment<NodeIdentity, TpcMessage>
} 
