include "seg_long_max_abs.dfy"

/** The purpose of this module is to abstract the 
*   different components of the closed_on_left 
*   modules so that we understand more easily how
*   they are reasoned and developed.
*/
abstract module AbstractClosedLeft refines SegLongMax {

    
    method mseg_long_max(v : array<T>) returns (r : int)
    ensures there_is_a_segment_that_long(v[..], r)
    ensures is_longest_segment(v[..], r)
    {
        var n, s;
        r, s, n := variable_initialization(v);
        
        while n < v.Length 
            decreases v.Length - n
            invariant 0 <= s <= n <= v.Length
            invariant r == seg_long_max(v[..], 0, n).0 
            invariant s == seg_long_max(v[..], 0, n).1
            {
                //We update (r), (s) and (n)
                s := update_actual_s(v, 0, s, n + 1);

                r := update_actual_seg_length(v, r, n, s);

                n := n + 1;
            }

            //Lemmas that ensures that the invariant implies the postconditions
            seg_long_max_existence(v[..], 0, v.Length);
            seg_long_max_snd(v[..], 0, v.Length);
    }

    /** Lemma which ensures that if a segment fulfills the property, then all its prefixes fulfill it
    *    as well.
    */
    lemma closed_on_left_lemma()
    ensures forall ini, fin, p, s : seq<T> | 0 <= ini <= p <= fin <= |s| && is_true_on_segment(s,ini,fin) :: is_true_on_segment(s,ini,p)

    /** Lemma that allow us to not neccesarily check the previous indexes when looking for candidates
    *    as lower bound of a segment with updated upper bound.
    */
        lemma no_need_to_come_back(s : seq<T>, ini : int, fin : int)
    requires 0 <= ini < fin <= |s|
    ensures forall p : int | ini <= p < seg_long_max(s, ini, fin).1 <= fin :: !is_true_on_segment(s, p, fin)
}