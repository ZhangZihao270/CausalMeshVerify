include "../Common/UpperBound.s.dfy"

module LiveTPC__Parameters_i {
import opened Common__UpperBound_s

datatype Parameters = Parameters(
    max_integer_val:UpperBound,
    coor_id:int
)

}