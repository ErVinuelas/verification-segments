include "unitary.dfy"

/** Example, the property we define is the one that 
*   checks wether all the elements of the segment are 
*   zero.
*/
module TestUnitary  refines SegLongMaxUnitary {
    type T = int

    ghost function is_true_on_elem(elem : T) : (bool)
    {
      elem==0
    }

    method m_true_on_segment(elem : T) returns (res : bool)
    {
        res := elem == 0;
    }

    /** We use this predicate as trigger for the postconditions for the
    *   following method.
    */
    ghost predicate within_limits(v : seq<int>, ini : int, fin : int)
    {
        0 <= ini <= fin <= |v|
    }

    method mseg_long_max_zero(a : array<int>) returns (r : int)
    ensures forall p, q | within_limits(a[..], p, q) &&  (forall k : int | p <= k < q :: a[k] == 0) :: q - p <= r
    ensures exists p, q | within_limits(a[..], p, q) && (forall k : int | p <= k < q :: a[k] == 0) :: q - p == r
    {
        r := mseg_long_max(a);
        
        if(exists p, q | within_limits(a[..], p, q) &&  (forall k : int | p <= k < q :: a[k] == 0) :: q - p > r)
        {
            var p, q :| within_limits(a[..], p, q) &&  (forall k : int | p <= k < q :: a[k] == 0) && q - p > r;

            assert is_true_on_segment(a[..], p, q);

            assert false;
        }

        if(forall p, q | within_limits(a[..], p, q) &&  (forall k : int | p <= k < q :: a[k] == 0) :: q - p < r)
        {
            var p, q :|  within_limits(a[..], p, q) && is_true_on_segment(a[..], p, q) && q - p == r;
            assert forall k : int | p <= k < q :: a[k] == 0;

            assert false;
        }
    }
}