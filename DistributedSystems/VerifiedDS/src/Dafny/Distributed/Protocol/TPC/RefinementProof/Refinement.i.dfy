include "StateMachine.i.dfy"
include "Assumptions.i.dfy"
include "../Types.i.dfy"
include "HandleRequest.i.dfy"
include "Decide.i.dfy"
include "Constants.i.dfy"
include "Requests.i.dfy"

module TpcRefinement__Refinement_i{
import opened TpcRefinement__DistributedSystem_i
import opened LiveTPC__DistributedSystem_i
import opened LiveTPC__Constants_i
import opened Temporal__Temporal_s
import opened Collections__Maps2_s
import opened Collections__Sets_i
import opened Collections__Seqs_s
import opened TpcRefinement__Assumptions_i
import opened Concrete_NodeIdentity_i
import opened LiveTPC__Types_i
import opened TpcRefinement__HandleRequest_i
import opened TpcRefinement__Decide_i
import opened TpcRefinement__Constants_i
import opened TpcRefinement__Requests_i
import opened AppStateMachine_s

lemma lemma_HostSeqNotEmpty(ps:TpcState)
  ensures |ps.constants.config.node_ids| > 0

lemma lemma_MapNonEmptySeqToSeqIsNonEmpty(s:seq<NodeIdentity>)
  requires |s| > 0
  ensures |set x | x in s :: x| > 0
// {
//   forall x | x in s
//   {
//     assert exists y :: y == x && y in s;
//   }
//   assert exists x :: x in s;
//   var ss := set x | x in s :: x;
//   assert forall x :: x in s ==> x in ss;
//   assert |ss| > 0;
// }

function GetServerAddresses(ps:TpcState):set<NodeIdentity>
  ensures |GetServerAddresses(ps)| > 0
  // ensures |GetServerAddresses(ps)| == |ps.constants.config.node_ids|
{
  lemma_HostSeqNotEmpty(ps);
  lemma_MapNonEmptySeqToSeqIsNonEmpty(ps.constants.config.node_ids);
  // MapSeqToSet(ps.constants.config.node_ids, x=>x)
  var s := set x | x in ps.constants.config.node_ids :: x;
  assert |s| > 0;
  s
}

function {:opaque} ConvertBehaviorSeqToImap<T>(s:seq<T>):imap<int, T>
  requires |s| > 0
  ensures  imaptotal(ConvertBehaviorSeqToImap(s))
  ensures  forall i :: 0 <= i < |s| ==> ConvertBehaviorSeqToImap(s)[i] == s[i]
{
  imap i {:trigger s[i]} :: if i < 0 then s[0] else if 0 <= i < |s| then s[i] else last(s)
}

function ProduceIntermediateAbstractState(server_addresses:set<NodeIdentity>, reqs:seq<Request>, req_in_reqs:int) : TPCSystemState
  requires |reqs| > 0
  requires 0 <= req_in_reqs <= |reqs|
  requires |server_addresses| > 0
  ensures ProduceIntermediateAbstractState(server_addresses, reqs, req_in_reqs) == ProduceAbstractState(server_addresses, reqs[..req_in_reqs])
{
  var requests := set req_num | 0 <= req_num < req_in_reqs :: reqs[req_num];
  
  // var appState := GetAppStateFromRequests(reqs[..req_in_reqs]);
  // var appState := AppHandleRequest(stateBeforePrevReq, reqs[req_in_reqs].req).0;
  // var reqs' := reqs[..req_in_reqs];
  // var requests' := set req_num | 0 <= req_num < |reqs'| :: reqs[req_num];
  // assert |requests| == |requests'|;
  // assert requests == requests';

  var replies := set req_num | 0 <= req_num < req_in_reqs :: GetReplyFromRequests_distributed(server_addresses, reqs, req_num);
  var reqs' := reqs[..req_in_reqs];
  var requests' := set req_num | 0 <= req_num < |reqs'| :: reqs[req_num];
  // var appState' := GetAppStateFromRequests(reqs');
  // assert appState == appState';
  assert requests == requests';
  assert req_in_reqs == |reqs'|;
  assert forall i :: 0 <= i < req_in_reqs ==> reqs[i] == reqs'[i];
  var replies' := set req_num | 0 <= req_num < |reqs'| :: GetReplyFromRequests_distributed(server_addresses, reqs', req_num);
  assert forall i :: 0 <= i < req_in_reqs ==> GetReplyFromRequests_distributed(server_addresses, reqs', i) == GetReplyFromRequests_distributed(server_addresses, reqs, i);
  assert replies == replies';

  // var appState' := GetAppStateFromRequests(reqs');
  // assert appState == appState';


  var tpcState := TPCSystemState(server_addresses, requests, replies);
  var tpcState' := TPCSystemState(server_addresses, requests', replies');
  assert tpcState == tpcState';
  tpcState
}

function ProduceAbstractState(server_addresses:set<NodeIdentity>, reqs:seq<Request>):TPCSystemState
  requires |server_addresses| > 0
{
  var requests := set req_num | 0 <= req_num < |reqs| :: reqs[req_num];
  var replies := set req_num | 0 <= req_num < |reqs| :: GetReplyFromRequests_distributed(server_addresses, reqs, req_num);
  TPCSystemState(server_addresses, requests, replies)
}


// lemma lemma_lemma(reqs:seq<Request>, votes:seq<Votes>)
//   requires |reqs| == |votes|
// {
//   forall opn | 0 <= opn < |reqs|
//   {
//     var reply1 := GetReplyFromRequests(reqs, opn);
//     var reply2 := GetReplyFromVotes(reqs, votes, opn);
//     assert reply1.client == reply2.client;
//     assert reply1.tid == reply2.tid;
//     assert reply1.rep == reply2.rep;
//     assert reply1 == reply2;
//   }
// }

predicate SystemRefinementRelation(s:TpcState, ts:TPCSystemState)
{
  exists qs :: IsMaximalQuorumOfVoteSequence(s, qs) && ts == ProduceAbstractState(GetServerAddresses(s), GetSequenceOfRequest(qs))
}

predicate TpcSystemBehaviorRefinementCorrectImap(
  b:Behavior<TpcState>,
  prefix_len:int,
  high_level_behavior:seq<TPCSystemState>
)
{
  && imaptotal(b)
  && |high_level_behavior| == prefix_len
  && (forall i :: 0 <= i < prefix_len ==> TpcSystemRefinement(b[i], high_level_behavior[i]))
  && |high_level_behavior| > 0
  && TpcSystemInit(high_level_behavior[0], MapSeqToSet(b[0].constants.config.node_ids, x=>x))
  && (forall i :: 0 <= i < |high_level_behavior| - 1 ==> TpcSystemNext(high_level_behavior[i], high_level_behavior[i+1]))
}

lemma lemma_GetBehaviorRefinementForBehaviorOfOneStep(
  b:Behavior<TpcState>,
  c:Constants
) returns (
  high_level_behavior:seq<TPCSystemState>
)
  requires imaptotal(b)
  requires TpcInit(b[0], c)
  ensures TpcSystemBehaviorRefinementCorrectImap(b, 1, high_level_behavior)
  ensures |high_level_behavior| == 1
  ensures SystemRefinementRelation(b[0], high_level_behavior[0])
{
  var qs := [];
  var rs := ProduceAbstractState(GetServerAddresses(b[0]), GetSequenceOfRequest(qs));
  if exists q :: IsValidQuorumOfVotes(b[0], q) && q.opn == 0
  {
    var q :| IsValidQuorumOfVotes(b[0], q) && q.opn == 0;
    var idx :| idx in q.indices;
    var packet := q.packets[idx];
    assert false;
  }
  assert IsMaximalQuorumOfVoteSequence(b[0], qs);
  assert SystemRefinementRelation(b[0], rs);
  high_level_behavior := [rs];
}

lemma lemma_ProduceAbstractStateSatisfiesRefinementRelation(
  b:Behavior<TpcState>,
  c:Constants,
  i:int,
  qs:seq<QuorumOfVotes>,
  rs:TPCSystemState
)
  requires IsValidBehaviorPrefix(b, c, i)
  requires 0 <= i
  requires IsMaximalQuorumOfVoteSequence(b[i], qs)
  requires rs == ProduceAbstractState(GetServerAddresses(b[i]), GetSequenceOfRequest(qs))
  ensures TpcSystemRefinement(b[i], rs)
{
  var ps := b[i];
  var reqs := GetSequenceOfRequest(qs);

  var server_addresses := GetServerAddresses(b[i]);

  lemma_ConstantsAllConsistent(b, c, i);

  forall p | p in ps.environment.sentPackets && p.src in rs.server_addresses && p.msg.ReplyMsg?
    ensures Reply(p.dst, p.msg.tid, p.msg.reply) in rs.replies
  {
    assert p.src in GetServerAddresses(ps);
    // assert p in b[i].environment.sentPackets;
    // assert p in b[i-1].environment.sentPackets;
    // qs', req_num can find a request that can produce the same reply as p
    var qs', reqs', req_num := lemma_ReplySentIsAllowed(server_addresses, b, c, i, p);

    var rs' := ProduceAbstractState(server_addresses, reqs');
    assert Reply(p.dst, p.msg.tid, p.msg.reply) in rs'.replies;

    // qs' and qs have the same request prefix
    lemma_RegularQuorumOfVoteSequenceIsPrefixOfMaximalQuorumOfVoteSequence(b, c, i, qs', qs);
    // requests in reqs' and reqs are the same
    lemma_GetReplyFromRequestsMatchesInSubsequence(server_addresses, reqs', reqs, req_num);

    // assert GetReplyFromRequests_distributed(server_addresses, reqs', req_num) == GetReplyFromRequests_distributed(server_addresses, reqs, req_num);

    // var rs' := ProduceAbstractState(server_addresses, reqs);
    assert Reply(p.dst, p.msg.tid, p.msg.reply) in rs'.replies;
  }

  forall req | req in rs.requests
    ensures exists p :: && p in ps.environment.sentPackets
                      && p.dst in rs.server_addresses
                      && p.msg.RequestMsg?
                      && req == Request(p.src, p.msg.tid, p.msg.req)
  {
    var req_num :| 0 <= req_num < |reqs| && req == reqs[req_num];
    var p := lemma_DecidedRequestWasSentByCLient(b, c, i, qs, reqs, req_num);
  }
}

// lemma lemma_DemonstrateTpcSystemNextWhenReqAdded(
//   server_addresses:set<NodeIdentity>,
//   s:TPCSystemState,
//   s':TPCSystemState,
//   reqs:seq<Request>,
//   reqs':seq<Request>
// ) 
// returns
// (
//   // intermediate_states:seq<TPCSystemState>,
//   req:Request
// )
//   requires s == ProduceAbstractState(server_addresses, reqs)
//   requires s' == ProduceAbstractState(server_addresses, reqs')
//   requires |reqs| <= |reqs'|
//   requires reqs'[..|reqs|] == reqs
//   ensures TpcStateSequenceReflectsRequestExecution(s, s', req)
//   ensures TpcSystemNext(s, s')
//   decreases |reqs'|
// {
//   if |reqs| == |reqs'| {
//     assert reqs == reqs';
//     assert s == s';
    
//     return;
//   }

//   var s_middle := ProduceAbstractState(server_addresses, all_but_last(reqs'));
//   var req_middle := lemma_DemonstrateTpcSystemNextWhenReqAdded(server_addresses, s, s_middle, reqs, all_but_last(reqs'));


// }

lemma lemma_FirstProduceIntermediateAbstractStateProducesAbstractState(
  server_addresses:set<NodeIdentity>,
  reqs:seq<Request>
)
  requires |reqs| > 0 
  requires |server_addresses| > 0
  ensures ProduceAbstractState(server_addresses, []) == 
          ProduceIntermediateAbstractState(server_addresses, reqs, 0)
{
  // var rs := ProduceAbstractState(server_addresses, all_but_last(reqs));
  // var rs' := ProduceIntermediateAbstractState(server_addresses, reqs, 0);

  // var requests := 
}

lemma lemma_LastProduceIntermediateAbstractStateProducesAbstractState(
  server_addresses:set<NodeIdentity>,
  reqs:seq<Request>
)
  requires |reqs| > 0
  requires |server_addresses| > 0
  ensures ProduceAbstractState(server_addresses, reqs) == ProduceIntermediateAbstractState(server_addresses, reqs, |reqs|)
{

}

lemma lemma_ProduceIntermediateAbstractStatesSatisfiesNext(
  server_addresses:set<NodeIdentity>,
  reqs:seq<Request>,
  req_in_reqs:int
)
returns 
(
  request:Request
)
  requires |reqs| > 0
  requires |server_addresses| > 0
  requires 0 <= req_in_reqs < |reqs|
  ensures request == reqs[req_in_reqs]
  ensures TpcSystemNextServerExecutesRequest(ProduceIntermediateAbstractState(server_addresses, reqs, req_in_reqs),
                                            ProduceIntermediateAbstractState(server_addresses, reqs, req_in_reqs+1), request)
{
  var rs := ProduceIntermediateAbstractState(server_addresses, reqs, req_in_reqs);
  var rs' := ProduceIntermediateAbstractState(server_addresses, reqs, req_in_reqs+1);

  request := reqs[req_in_reqs];
  var reply := GetReplyFromRequests_distributed(server_addresses, reqs, req_in_reqs);
}

// lemma lemma_DemonstrateTpcSystemNextWhenReqsExtened(
//   server_addresses:set<NodeIdentity>,
//   s:TPCSystemState,
//   s':TPCSystemState,
//   reqs:seq<Request>,
//   count:int
// )
// returns
// (
//   intermediate_states:seq<TPCSystemState>,
//   requests:seq<Request>
// )
//   requires |reqs| > 0
//   requires 0 <= count <= |reqs|
//   requires s == ProduceIntermediateAbstractState(server_addresses, reqs, 0)
//   requires s' == ProduceIntermediateAbstractState(server_addresses, reqs, count)
//   ensures TpcStateSequenceReflectsRequestsExecution(s, s', intermediate_states, requests)
//   ensures TpcSystemNext(s, s')
//   decreases count
// {
//   if count == 0 {
//     assert s' == s;
//     intermediate_states := [s];
//     requests := [];
//     assert TpcStateSequenceReflectsRequestsExecution(s, s', intermediate_states, requests);
//     return;
//   }

//   var s_middle := ProduceIntermediateAbstractState(server_addresses, reqs, count-1);
//   var intermediate_states_middle, requests_middle := lemma_DemonstrateTpcSystemNextWhenReqsExtened(server_addresses, s, s_middle, reqs, count - 1);

//   intermediate_states := intermediate_states_middle + [s'];
//   var next_request := lemma_ProduceIntermediateAbstractStatesSatisfiesNext(server_addresses, reqs, count-1);
//   requests := requests_middle + [next_request];
//   assert TpcSystemNextServerExecutesRequest(s_middle, s', next_request);
//   assert TpcStateSequenceReflectsRequestsExecution(s, s', intermediate_states, requests);
// }

lemma lemma_DemonstrateTpcSystemNextWhenReqsExtened(
  server_addresses:set<NodeIdentity>,
  s:TPCSystemState,
  s':TPCSystemState,
  reqs:seq<Request>,
  i:int,
  j:int
)
returns
(
  intermediate_states:seq<TPCSystemState>,
  requests:seq<Request>
)
  requires |reqs| > 0
  requires |server_addresses| > 0
  requires 0 <= i <= j <= |reqs|
  requires s == ProduceIntermediateAbstractState(server_addresses, reqs, i)
  requires s' == ProduceIntermediateAbstractState(server_addresses, reqs, j)
  ensures TpcStateSequenceReflectsRequestsExecution(s, s', intermediate_states, requests)
  ensures TpcSystemNext(s, s')
  decreases j-i
{
  if j-i == 0 {
    assert s' == s;
    intermediate_states := [s];
    requests := [];
    assert TpcStateSequenceReflectsRequestsExecution(s, s', intermediate_states, requests);
    return;
  }

  var s_middle := ProduceIntermediateAbstractState(server_addresses, reqs, j-1);
  var intermediate_states_middle, requests_middle := lemma_DemonstrateTpcSystemNextWhenReqsExtened(server_addresses, s, s_middle, reqs, i, j - 1);
  assert TpcStateSequenceReflectsRequestsExecution(s, s_middle, intermediate_states_middle, requests_middle);
  assert intermediate_states_middle[|intermediate_states_middle|-1] == s_middle;

  intermediate_states := intermediate_states_middle + [s'];
  var next_request := lemma_ProduceIntermediateAbstractStatesSatisfiesNext(server_addresses, reqs, j-1);
  assert TpcStateSequenceReflectsRequestsExecution(s_middle, s', [s_middle] + [s'], [next_request]);

  requests := requests_middle + [next_request];

  lemma_TpcSystemNextConcat(server_addresses, s, s_middle, s', intermediate_states_middle, [s_middle] + [s'], requests_middle, [next_request]);
  assert TpcSystemNextServerExecutesRequest(s_middle, s', next_request);
  assert TpcStateSequenceReflectsRequestsExecution(s, s', intermediate_states, requests);
}

lemma lemma_TpcSystemNextConcat(
  server_addresses:set<NodeIdentity>,
  s0:TPCSystemState,
  s1:TPCSystemState,
  s2:TPCSystemState,
  states0:seq<TPCSystemState>,
  states1:seq<TPCSystemState>,
  reqs0:seq<Request>,
  reqs1:seq<Request>
)
  requires TpcStateSequenceReflectsRequestsExecution(s0, s1, states0, reqs0);
  requires TpcStateSequenceReflectsRequestsExecution(s1, s2, states1, reqs1);
  ensures var states2 := all_but_last(states0) + states1; var reqs2 := reqs0 + reqs1;
          TpcStateSequenceReflectsRequestsExecution(s0, s2, states2, reqs2)

lemma lemma_DemonstrateTpcSystemNextWhenReqAdded(
  server_addresses:set<NodeIdentity>,
  s:TPCSystemState,
  s':TPCSystemState,
  reqs:seq<Request>,
  reqs':seq<Request>
) 
returns
(
  intermediate_states:seq<TPCSystemState>,
  requests:seq<Request>
)
  requires |server_addresses| > 0
  requires s == ProduceAbstractState(server_addresses, reqs)
  requires s' == ProduceAbstractState(server_addresses, reqs')
  requires |reqs| <= |reqs'|
  requires reqs'[..|reqs|] == reqs
  ensures TpcStateSequenceReflectsRequestsExecution(s, s', intermediate_states, requests)
  ensures TpcSystemNext(s, s')
  decreases |reqs'|
{
  if |reqs| == |reqs'| {
    assert reqs == reqs';
    assert s == s';
    intermediate_states := [s];
    requests := [];
    assert TpcStateSequenceReflectsRequestsExecution(s, s', intermediate_states, requests);
    return;
  }

  var s_middle := ProduceAbstractState(server_addresses, all_but_last(reqs'));
  assert all_but_last(reqs') == reqs'[..|reqs'|-1];
  assert s_middle == ProduceIntermediateAbstractState(server_addresses, reqs', |reqs'|-1);
  var intermediate_states_middle, req_middle := lemma_DemonstrateTpcSystemNextWhenReqAdded(server_addresses, s, s_middle, reqs, all_but_last(reqs'));
  assert TpcStateSequenceReflectsRequestsExecution(s, s_middle, intermediate_states_middle, req_middle);

  lemma_FirstProduceIntermediateAbstractStateProducesAbstractState(server_addresses, reqs');
  lemma_LastProduceIntermediateAbstractStateProducesAbstractState(server_addresses, reqs');
  var intermediate_states_next, reqs_next := lemma_DemonstrateTpcSystemNextWhenReqsExtened(server_addresses, s_middle, s', reqs', |reqs'|-1, |reqs'|);
  assert TpcStateSequenceReflectsRequestsExecution(s_middle, s', intermediate_states_next, reqs_next);
  
  intermediate_states := all_but_last(intermediate_states_middle) + intermediate_states_next;
  requests := req_middle + reqs_next;
  lemma_TpcSystemNextConcat(server_addresses, s, s_middle, s', intermediate_states_middle, intermediate_states_next, req_middle, reqs_next);
  assert TpcStateSequenceReflectsRequestsExecution(s, s', intermediate_states, requests);
}

lemma lemma_GetBehaviorRefinementForPrefix(
  b:Behavior<TpcState>,
  c:Constants,
  i:int
) returns (
  high_level_behavior:seq<TPCSystemState>
)
  requires 0 <= i 
  requires IsValidBehaviorPrefix(b,c,i)
  ensures TpcSystemBehaviorRefinementCorrectImap(b, i+1, high_level_behavior)
  ensures SystemRefinementRelation(b[i], last(high_level_behavior))
{
  if i == 0 
  {
    high_level_behavior := lemma_GetBehaviorRefinementForBehaviorOfOneStep(b, c);
    return;
  }

  lemma_ConstantsAllConsistent(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  assert GetServerAddresses(b[i-1]) == GetServerAddresses(b[i]);
  var server_addresses := GetServerAddresses(b[i-1]);

  var prev_high_level_behavior := lemma_GetBehaviorRefinementForPrefix(b, c, i-1);
  var prev_rs := last(prev_high_level_behavior);
  var prev_qs :| && IsMaximalQuorumOfVoteSequence(b[i-1], prev_qs)
                  && prev_rs == ProduceAbstractState(server_addresses, GetSequenceOfRequest(prev_qs));
  var prev_reqs := GetSequenceOfRequest(prev_qs);
  
  var qs := lemma_GetMaximalQuorumOfVotes(b, c, i);
  var reqs := GetSequenceOfRequest(qs);

  lemma_IfValidQuorumOfVotesSequenceNowThenNext(b, c, i-1, prev_qs);
  lemma_RegularQuorumOfVoteSequenceIsPrefixOfMaximalQuorumOfVoteSequence(b, c, i, prev_qs, qs);

  var s' := ProduceAbstractState(server_addresses, reqs);
  var intermediate_states, req := lemma_DemonstrateTpcSystemNextWhenReqAdded(server_addresses, last(prev_high_level_behavior), s', prev_reqs, reqs);
  // var req := lemma_DemonstrateTpcSystemNextWhenReqAdded(server_addresses, last(prev_high_level_behavior), s', prev_reqs, reqs);

  high_level_behavior := prev_high_level_behavior + [s'];
  lemma_ProduceAbstractStateSatisfiesRefinementRelation(b, c, i, qs, last(high_level_behavior));
}

lemma lemma_VotesCanGenerateTheSameReply(
  b:Behavior<TpcState>,
  c:Constants,
  i:int
)
  requires 0 <= i 
  requires IsValidBehaviorPrefix(b, c, i)
{
  if i == 0 
  {
    var high_level_behavior := lemma_GetBehaviorRefinementForBehaviorOfOneStep(b, c);
    return;
  }

  lemma_ConstantsAllConsistent(b, c, i-1);
  lemma_ConstantsAllConsistent(b, c, i);
  assert GetServerAddresses(b[i-1]) == GetServerAddresses(b[i]);
  var server_addresses := GetServerAddresses(b[i-1]);

  var qs := lemma_GetMaximalQuorumOfVotes(b, c, i);
  var reqs := GetSequenceOfRequest(qs);
  var votes := GetSequenceOfVotes(qs);

  // lemma_lemma(reqs, votes);
}

// for behavior of protocol, if a bahavior of abstraction can be found, i guess the refinement is true.
lemma lemma_GetBehaviorRefinement(
    low_level_behavior:seq<TpcState>,
    c:Constants
) returns (
    high_level_behavior:seq<TPCSystemState>
)
    requires |low_level_behavior| > 0
    requires TpcInit(low_level_behavior[0], c)
    requires forall i :: 0 <= i < |low_level_behavior| - 1 ==> TpcNext(low_level_behavior[i], low_level_behavior[i+1])
    ensures TpcSystemBehaviorRefinementCorrect(MapSeqToSet(c.config.node_ids, x=>x), low_level_behavior, high_level_behavior)
{
    var b := ConvertBehaviorSeqToImap(low_level_behavior);

    high_level_behavior := lemma_GetBehaviorRefinementForPrefix(b, c, |low_level_behavior|-1);
}

}