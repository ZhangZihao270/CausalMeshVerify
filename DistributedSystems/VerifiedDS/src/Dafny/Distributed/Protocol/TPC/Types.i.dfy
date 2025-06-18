include "../Common/NodeIdentity.i.dfy"
include "../../Services/TPC/AppStateMachine.s.dfy"

module LiveTPC__Types_i {

import opened Concrete_NodeIdentity_i
import opened AppStateMachine_s

type TxnNumber = int

datatype Request = Request(client:NodeIdentity, tid:TxnNumber, req:AppRequest)

datatype Reply = Reply(client:NodeIdentity, tid:TxnNumber, rep:AppReply)

type ReplyCache = map<NodeIdentity, Reply>

// // the first int is decision: 0 -> not decided, 1 -> commit, 2 -> abort
// // the second seq<int> is votes from participants: 0 -> yes, 1 -> no
// type CoordinatorHistoryEntry = (int, seq<int>)

// // the first int is decision it received during the commit phase: 0 -> not decided, 1 -> commit, 2 -> abort
// // the second int is its vote: 0 -> yes, 1 -> no
// type ParticipantHistroyEntry = (int, int)
}