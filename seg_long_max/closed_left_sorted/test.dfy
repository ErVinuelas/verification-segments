include "closed_left_sorted.dfy"

/** Concrete example with the property that 
*   checks if all the elements of the segment 
*   are greater that the first one.
*/
module TestClosedLeftSorted refines SegLongMaxClosedLeftSorted{

    const k : int := 4

    ghost function is_true_on_segment(v : seq<T>, ini : int, fin : int) : (bool)
    {
        if(ini == fin) then true else v[fin - 1] - v[ini] < k
    }

    method m_true_on_segment(v : array<T>, ini : int, fin : int) returns (res : bool)
    {
        res := true;
        if(ini != fin) { res :=  v[fin - 1] - v[ini] < k;   }
    }

    ghost predicate within_limits(v : seq<int>, ini : int, fin : int)
    {
        0 <= ini < fin <= |v|
    }

    //We ensure that the lemmas defined in the abstract modules are true
    lemma closed_on_left_lemma(s : seq<T>)
    {}
 
    lemma prop_is_true_on_void(v : seq<T>)
    ensures forall p | 0 <= p <= |v| :: is_true_on_segment(v, p, p)
    {}

    method mseg_long_max_zero(a : array<int>) returns (r : int)
    requires sorted(a[..])
    requires exists p, q | within_limits(a[..], p, q) && (a[q - 1] - a[p] < k) :: q - p > 1
    ensures forall p, q | within_limits(a[..], p, q) && (a[q - 1] - a[p] < k) :: q - p <= r
    ensures exists p, q | within_limits(a[..], p, q) && (a[q - 1] - a[p] < k) :: q - p == r
    {
        r := mseg_long_max(a);
        
        if(exists p, q | within_limits(a[..], p, q) &&  (a[q - 1] - a[p] < k) :: q - p > r)
        {
            var p, q :| within_limits(a[..], p, q) && (a[q - 1] - a[p] < k) && q - p > r;

            assert is_true_on_segment(a[..], p, q);

            assert false;
        }

        if(forall p, q | within_limits(a[..], p, q) &&  (a[q - 1] - a[p] < k) :: q - p < r)
        {
            var p, q :|  within_limits(a[..], p, q) && is_true_on_segment(a[..], p, q) && q - p == r;

            assert forall p, k | within_limits(a[..], p, q) :: (a[q - 1] - a[p] < k); 

            assert false;
        }
    }
}