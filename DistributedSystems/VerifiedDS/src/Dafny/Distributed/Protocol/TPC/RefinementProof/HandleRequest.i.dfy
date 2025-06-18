include "../DistributedSystem.i.dfy"
include "../../../Services/TPC/AppStateMachine.s.dfy"
include "StateMachine.i.dfy"

module TpcRefinement__HandleRequest_i {
import opened LiveTPC__DistributedSystem_i
import opened LiveTPC__Types_i
import opened LiveTPC__Coordinator_i
import opened LiveTPC__Participant_i
import opened Collections__Seqs_s
import opened AppStateMachine_s
import opened Concrete_NodeIdentity_i
import opened TpcRefinement__DistributedSystem_i

// predicate AllVotesAreYesSimulator(votes:seq<int>)
// {
//   forall v :: v in votes ==> v == 0
// }

// function CoordinatorMakeDecisionSimulator(votes:seq<int>) : int
// {
//   if AllVotesAreYesSimulator(votes) then
//     1
//   else
//     2
// }

// function CoordinatorGenerateReplySimulator(req:Request, decision:int) : Reply
// {
//   if decision == 1 then
//     Reply(req.client, req.tid, Commit())
//   else
//     Reply(req.client, req.tid, Abort())
// }

function HandleRequestInDistributedWay_helper(n:int, req:AppRequest):seq<int>
  requires n >= 0
  ensures var votes := HandleRequestInDistributedWay_helper(n,req); 
          var vote := AppHandleRequest(req);
          && (forall v :: v in votes ==> v == vote)
          && |votes| == n
{
  if n == 0 then
    []
  else
    // var (state, vote) := AppHandleRequest(s,req);
    var vote := ParticipantMakeVote(req);
    var vote_rest := HandleRequestInDistributedWay_helper(n-1,req);
    vote_rest + [vote]
}

lemma lemma_DecisionMadeByCoordinatorIsSameAsMadeCentralized(votes:seq<int>, decision:int)
  ensures CoorMakeDecision(votes) == decision

function HandleRequestInDistributedWay(server_addresses:set<NodeIdentity>, req:AppRequest):seq<int>
  requires |server_addresses| > 0
  ensures var votes := HandleRequestInDistributedWay(server_addresses, req);
          var decision := HandleRequest(req);
          && CoorMakeDecision(votes) == decision
          && |votes| == |server_addresses|
{
  var n := |server_addresses|;
  var votes := HandleRequestInDistributedWay_helper(n, req);

  // ghost var temp := AppHandleRequest(s, req);
  // assert forall v :: v in votes ==> v == temp.1;

  ghost var dec := HandleRequest(req);
  lemma_DecisionMadeByCoordinatorIsSameAsMadeCentralized(votes, dec);


  // var decision := CoordinatorMakeDecision(votes);

  // var reply := CoordinatorGenerateReplySimulator(req,)
  votes
}

// function HandleRequestInDistributedWay(server_addresses:seq<NodeIdentity>, req:AppRequest):seq<int>
//   requires |server_addresses| > 0
//   ensures var votes := HandleRequestInDistributedWay(server_addresses, req);
//           var decision := HandleRequest(req);
//           && CoorMakeDecision(votes) == decision
//           && |votes| == |server_addresses|
// {
//   var n := |server_addresses|;
//   var votes := HandleRequestInDistributedWay_helper(n, req);

//   // ghost var temp := AppHandleRequest(s, req);
//   // assert forall v :: v in votes ==> v == temp.1;

//   ghost var dec := HandleRequest(req);
//   lemma_DecisionMadeByCoordinatorIsSameAsMadeCentralized(votes, dec);


//   // var decision := CoordinatorMakeDecision(votes);

//   // var reply := CoordinatorGenerateReplySimulator(req,)
//   votes
// }

// function GetAppStateFromRequests(reqs:seq<Request>):AppState
// {
//     if |reqs| == 0 then
//         AppInitialize()
//     else
//         AppHandleRequest(GetAppStateFromRequests(all_but_last(reqs)), last(reqs).req).0
// }

function GetReplyFromRequests(reqs:seq<Request>, req_num:int):Reply
  requires 0 <= req_num < |reqs|
{
  // var prev_state := GetAppStateFromRequests(reqs[..req_num]);
  var req := reqs[req_num];
  var result := AppHandleRequest(req.req);
  if result == 0 then
    Reply(req.client, req.tid, Commit())
  else
    Reply(req.client, req.tid, Abort())
}

function GetReplyFromRequests_distributed(server_addresses:set<NodeIdentity>, reqs:seq<Request>, req_num:int):Reply
  requires 0 <= req_num < |reqs|
  requires |server_addresses| > 0
{
  // var prev_state := GetAppStateFromRequests(reqs[..req_num]);
  var req := reqs[req_num];
  var votes := HandleRequestInDistributedWay(server_addresses, req.req);
  var decision := CoorMakeDecision(votes);
  var reply := CoordinatorGenerateReply(req, decision);
  reply
}

// function GetReplyFromRequests_distributed(server_addresses:seq<NodeIdentity>, reqs:seq<Request>, req_num:int):Reply
//   requires 0 <= req_num < |reqs|
//   requires |server_addresses| > 0
// {
//   // var prev_state := GetAppStateFromRequests(reqs[..req_num]);
//   var req := reqs[req_num];
//   var votes := HandleRequestInDistributedWay(server_addresses, req.req);
//   var decision := CoorMakeDecision(votes);
//   var reply := CoordinatorGenerateReply(req, decision);
//   reply
// }


// lemma lemma_GetReplyFromRequestsMatchesInSubsequence(
//     server_addresses:set<NodeIdentity>,
//     reqs1:seq<Request>,
//     reqs2:seq<Request>,
//     req_num:int
// )
//     requires |server_addresses| > 0 
//     requires 0 <= req_num < |reqs1| <= |reqs2|
//     requires reqs1 == reqs2[..|reqs1|]
//     requires 0 <= req_num < |reqs1|
//     ensures GetReplyFromRequests_distributed(server_addresses, reqs1, req_num) == GetReplyFromRequests_distributed(server_addresses, reqs2, req_num)
// {

// }

lemma lemma_GetReplyFromRequestsMatchesInSubsequence(
    server_addresses:set<NodeIdentity>,
    reqs1:seq<Request>,
    reqs2:seq<Request>,
    req_num:int
)
    requires |server_addresses| > 0 
    requires 0 <= req_num < |reqs1| <= |reqs2|
    requires reqs1 == reqs2[..|reqs1|]
    requires 0 <= req_num < |reqs1|
    ensures GetReplyFromRequests_distributed(server_addresses, reqs1, req_num) == GetReplyFromRequests_distributed(server_addresses, reqs2, req_num)
{

}
}