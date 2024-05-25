include "relation.dfy"

/** Concrete example. The relation we define is 
*   the comparison (less) between two integers.
*/
module TestRelation refines SegLongMaxRelation {
    //We fix the type we will be using
    type T = int

    ghost function is_true_relation(elem1 : T, elem2 : T) : (bool)
    {
      elem1 <= elem2
    }

    method m_true_relation(elem1 : T, elem2 : T) returns (res : bool)
    {
        res := elem1 <= elem2;
    }

    //We prove the needed lemmas
    lemma it_composes_segments(s : seq<T>)
    {
        if(exists ini : int, fin : int | 0 <= ini < fin <= |s| :: !composes_segments(s, ini, fin)){
            var  ini : int, fin : int :| 0 <= ini < fin <= |s| && !composes_segments(s, ini, fin);

            if(ini + 1 < fin && !is_true_on_segment(s, ini, fin)){
                var i, j, k :| ini <= i < j < k <= fin && !(is_true_on_segment(s, i, j + 1) && is_true_on_segment(s, j, k) ==> is_true_on_segment(s, i, k));
                if(is_true_on_segment(s, i, j + 1) && is_true_on_segment(s, j, k)){
                    assert s[j] <= s[k];
                    assert s[i] <= s[i];
                }
                assert false;
            }
        }

        assert forall ini : int, fin : int | 0 <= ini < fin <= |s| :: composes_segments(s, ini, fin);

    }

    /** We use this predicate as trigger for the postconditions for the
    *   following method.
    */
    ghost predicate within_limits(v : seq<int>, ini : int, fin : int)
    {
        0 <= ini <= fin <= |v|
    }

    method mseg_long_max_zero(a : array<int>) returns (r : int)
    ensures forall p, q | within_limits(a[..], p, q) && (forall k1, k2 | p <= k1 < k2 < q :: a[k1] <= a[k2]) :: q - p <= r
    ensures exists p, q | within_limits(a[..], p, q) && (forall k1, k2 | p <= k1 < k2 < q :: a[k1] <= a[k2]) :: q - p == r
    {
        r := mseg_long_max(a);
        
        //Proof that our postconditions corresponds with the ones specified by the user.
        if(exists p, q | within_limits(a[..], p, q) &&  (forall k1, k2 | p <= k1 < k2 < q :: a[k1] <= a[k2]) :: q - p > r)
        {
            var p, q :| within_limits(a[..], p, q) &&  (forall k1, k2 | p <= k1 < k2 < q :: a[k1] <= a[k2]) && q - p > r;

            assert is_true_on_segment(a[..], p, q);

            assert false;
        }

        if(forall p, q | within_limits(a[..], p, q) &&  (forall k1, k2 | p <= k1 < k2 < q :: a[k1] <= a[k2]) :: q - p < r)
        {
            var p, q :|  within_limits(a[..], p, q) && is_true_on_segment(a[..], p, q) && q - p == r;
            assert forall k1, k2 | p <= k1 < k2 < q :: a[k1] <= a[k2];

            assert false;
        }
    }
}
