include "unitary.dfy"

/** Concrete example for the property that
*   checks if all the elements of the segment are 
*   zero.
*/
module TestContSeg refines ContSegForAllP {
    type T = int

    ghost function is_true_on_elem(elem : T) : bool
    {
        elem == 0
    }

    method m_is_true_elem(elem : T) returns (res : bool)
    {
        res := elem == 0;
    }

    method m_all_zero(v : array<int>, l : int) returns (r : int)
    requires 1 <= l <= v.Length
    ensures r == |set p, q | 0 <= p < q <= v.Length && (forall k | p <= k < q :: v[k] == 0) :: (p, q)|
    {
        r := mcount_seg(v);
        valid_segments_snd(v[..], 0, v.Length);

        var set1 := set p, q | 0 <= p < q <= v.Length && is_true_on_segment(v[..], p, q) :: (p, q);
        var set2 := set p, q | 0 <= p < q <= v.Length && (forall k | p <= k < q :: v[k] == 0) :: (p, q);

        assert set1 == set2;
    }
}