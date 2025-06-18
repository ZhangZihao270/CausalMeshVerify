include "Configuration.i.dfy"
include "Parameters.i.dfy"

module LiveTPC__Constants_i {
import opened LiveTPC__Configuration_i
import opened LiveTPC__Parameters_i

datatype Constants = Constants(
  config:Configuration,
  params:Parameters
  )

datatype HostConstants = HostConstants(
  my_index:int,
  all:Constants
  )

predicate HostConstantsValid(c:HostConstants)
{
  0 <= c.my_index < |c.all.config.node_ids|
}

}