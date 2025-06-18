include "../DistributedSystem.i.dfy"

module TpcRefinement__Quorum_i {
import opened LiveTPC__Constants_i
import opened LiveTPC__Configuration_i
import opened LiveTPC__Message_i
import opened Concrete_NodeIdentity_i
import opened Collections__Sets_i

lemma lemma_GetIndicesFromNodes(nodes:set<NodeIdentity>, config:Configuration) returns (indices:set<int>)
    requires WellFormedLConfiguration(config)
    requires forall node :: node in nodes ==> node in config.node_ids
    ensures forall idx :: idx in indices ==> 0 <= idx < |config.node_ids| && config.node_ids[idx] in nodes
    ensures forall node :: node in nodes ==> GetNodeIndex(node, config) in indices
    ensures |indices| == |nodes|
{
    indices := set idx | 0 <= idx < |config.node_ids| && config.node_ids[idx] in nodes;
    var f := (idx =>
            if (idx >= 0 && idx < |config.node_ids|) then
                config.node_ids[idx]
            else
                var end:NodeIdentity :| (true); end);
    forall idx1, idx2 | idx1 in indices && idx2 in indices  && f(idx1) in nodes && f(idx2) in nodes && f(idx1) == f(idx2)
    {
        assert NodesDistinct(config.node_ids, idx1, idx2);
    }
    forall node | node in nodes
        ensures exists idx :: idx in indices && node == f(idx)
    {
        var idx := GetNodeIndex(node, config);
        assert idx in indices && node == f(idx);
    }
    lemma_MapSetCardinalityOver(indices, nodes, f);
}
}