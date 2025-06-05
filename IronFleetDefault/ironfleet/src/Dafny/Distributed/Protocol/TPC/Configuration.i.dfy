include "Types.i.dfy"
include "../../Common/Collections/Sets.i.dfy"
include "../../Common/Collections/Seqs.i.dfy"

module LiveTPC__Configuration_i {
import opened LiveTPC__Types_i
import opened Collections__Sets_i
import opened Collections__Seqs_i
import opened Concrete_NodeIdentity_i

datatype Configuration = Configuration(
    node_ids:seq<NodeIdentity>
)

function NodesSize(c:Configuration) :int 
{
    if |c.node_ids| > 0 then
        |c.node_ids|
    else
        1
}

predicate NodesDistinct(nodes:seq<NodeIdentity>, i:int, j:int)
{
    0 <= i < |nodes| && 0 <= j < |nodes| && nodes[i] == nodes[j] ==> i == j
}

predicate NodesIsUnique(nodes:seq<NodeIdentity>)
{
    forall i,j :: 0 <= i < |nodes| && 0 <= j < |nodes| && nodes[i] == nodes[j] ==> i == j
}

predicate WellFormedLConfiguration(c:Configuration)
{
    && 0 < |c.node_ids|
    && (forall i,j :: NodesDistinct(c.node_ids,i,j))
    && NodesIsUnique(c.node_ids)
}

predicate IsNodeIndex(idx:int, id:NodeIdentity, c:Configuration)
{
    && 0 <= idx < |c.node_ids|
    && c.node_ids[idx] == id
}

function GetNodeIndex(id:NodeIdentity, c:Configuration):int
    requires id in c.node_ids
    ensures var idx := GetNodeIndex(id, c);
            IsNodeIndex(idx,id,c)
{
    FindIndexInSeq(c.node_ids, id)
}

}