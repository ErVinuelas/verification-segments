include "unitary.dfy"


module TestSlidingWindow refines SlidingWindowForAllP {
    type T = int

    ghost function is_true_on_elem(elem : T) : bool
    {
        elem % 2 == 0
    }

    method m_is_true_elem(elem : T) returns (res : bool)
    {
        res := elem % 2 == 0;
    }

    method m_all_zero(v : array<int>, l : int) returns (r : int)
    requires 1 <= l <= v.Length
    ensures r == |set p | 0 <= p - l < p <= v.Length && (forall k | p - l <= k < p :: v[k] % 2 == 0) :: (p - l, p)|
    {
        r := mcount_seg(v, l);
        valid_segments_snd(v[..], 0, v.Length, l);

        var set1 := set p | 0 <= p - l < p <= v.Length && is_true_on_segment(v[..], p - l, p) :: (p - l, p);
        var set2 := set p | 0 <= p - l < p <= v.Length && (forall k | p - l <= k < p :: v[k] % 2 == 0) :: (p - l, p);

        assert set1 == set2;
    }
}