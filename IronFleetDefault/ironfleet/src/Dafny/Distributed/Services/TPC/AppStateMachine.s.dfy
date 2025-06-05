include "../../Common/Native/Io.s.dfy"

module AppStateMachine_s{
import opened Native__NativeTypes_s
import opened Native__Io_s

type Bytes = seq<byte>
type AppState = uint64
datatype AppRequest' = AppRequest(tid:uint64)
datatype AppReply' = Commit() | Abort()

type AppRequest = AppRequest'
type AppReply = AppReply'

function method AppInitialize() : AppState { 0 }

// function method AppHandleRequest(m:AppState, request:AppRequest) : (AppState, int)
//     // requires 0 <= nid <= 3
// {
//     (0, MakeVote(request.tid))
// }

function method AppHandleRequest(request:AppRequest) : (int)
    // requires 0 <= nid <= 3
{
    MakeVote(request.tid)
}


function method MakeVote(tid:uint64) : int
    // requires 0 <= nid <= 3
{
    if (tid <= 0xffff_ffff_ffff_ffff) then
        var k :=  tid % 100;
        if k == 1 then
            1
        else
            0
    else
        1
}

// function {:axiom} AppInitialize() : AppState
// function {:axiom} AppHandleRequest(m:AppState, request:AppRequest) : (AppState, AppReply)
// function method MaxAppRequestSize() : int  { 0x800_0000 }            // 128 MB
// function method MaxAppReplySize() : int    { 0x800_0000 }            // 128 MB
// function method MaxAppStateSize() : int    { 0x1000_0000_0000_0000 } // 2^60 B

// class AppStateMachine
// {
//   constructor{:axiom} ()
//     requires false

//   function {:axiom} Abstractify() : AppState

//   static method {:axiom} Initialize() returns (m:AppStateMachine)
//     ensures fresh(m)
//     ensures m.Abstractify() == AppInitialize()

//   static method {:axiom} Deserialize(state:AppState) returns (m:AppStateMachine)
//     ensures fresh(m)
//     ensures m.Abstractify() == state

//   method {:axiom} Serialize() returns (state:AppState)
//     ensures state == Abstractify()
//     ensures |state| <= MaxAppStateSize()

//   method {:axiom} HandleRequest(request:AppRequest) returns (reply:AppReply)
//     requires |request| <= MaxAppRequestSize()
//     ensures  (Abstractify(), reply) == AppHandleRequest(old(Abstractify()), request)
//     ensures  |reply| <= MaxAppReplySize()
// }

}