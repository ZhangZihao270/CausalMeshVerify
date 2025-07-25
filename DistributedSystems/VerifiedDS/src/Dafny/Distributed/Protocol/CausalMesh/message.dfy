include "types.dfy"
include "../../Common/Framework/Environment.s.dfy"

module CausalMesh_Message_i {
    import opened CausalMesh_Types_i
    import opened Environment_s

    datatype Message = 
        //   Message_Invalid()
          Message_Read(opn_read:int, key_read:Key, deps_read:Dependency)
        | Message_Read_Reply(opn_rreply:int, key_rreply:Key, vc_rreply:VectorClock, deps_rreply:Dependency)
        | Message_Write(opn_write:int, key_write:Key, deps_write:Dependency, local:map<Key, Meta>)
        | Message_Write_Reply(opn_wreply:int, key_wreply:Key, vc_wreply:VectorClock)
        // | Message_Propagation(key:Key, metas:set<Meta>, start:int)
        | Message_Propagation(key:Key, meta:Meta, start:int)

    predicate MessageValid(m:Message)
    {
        match m 
            // case Message_Invalid() => true
            case Message_Read(_,key_read, deps_read) => key_read in Keys_domain && DependencyValid(deps_read)
            case Message_Read_Reply(_,key_rreply, vc_rreply, deps_rreply) => key_rreply in Keys_domain && VectorClockValid(vc_rreply) && DependencyValid(deps_rreply)
            case Message_Write(_,key_write, deps_write, local) => key_write in Keys_domain && DependencyValid(deps_write) && (forall k :: k in local ==> MetaValid(local[k]))
            case Message_Write_Reply(_,key_wreply, vc_wreply/*, deps_wreply*/) => key_wreply in Keys_domain && VectorClockValid(vc_wreply) // && DependencyValid(deps_wreply)
            case Message_Propagation(key, meta, start) => key in Keys_domain && (MetaValid(meta) && meta.key == key) && 0 <= start < Nodes
    }

    // datatype Packet = Packet(src:int, dst:int, msg:Message)
    type Packet = LPacket<int, Message>
    type CMEnvironment = LEnvironment<int, Message>
    type CMIo = LIoOp<int, Message>

    predicate PacketValid(p:Packet)
    {
        && MessageValid(p.msg)
    }

    predicate PacketHasCorrectSrcAndDst(p:Packet)
    {
        match p.msg 
            case Message_Read(_,_,_) => 0 <= p.src < Clients && 0 <= p.dst < Nodes
            case Message_Read_Reply(_,_,_,_) => 0 <= p.dst < Clients && 0 <= p.src < Nodes
            case Message_Write(_,_,_,_) => 0 <= p.src < Clients && 0 <= p.dst < Nodes
            case Message_Write_Reply(_,_,_) => 0 <= p.dst < Clients && 0 <= p.src < Nodes
            case Message_Propagation(_,_,_) => 0 <= p.src < Nodes && 0 <= p.dst < Nodes && NodesAreNext(p.src, p.dst)
    }
}