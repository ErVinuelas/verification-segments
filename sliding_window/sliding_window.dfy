/** This module represents the abstract methods that are required to
*   solve in an iterative way a problem that tries to find the number
*   of segments of a fixed length that fulfills a property over a vector.
*
*   The functions used in this module are very similar to the ones used at
*   cont_seg/count_seg.dfy.
*/

abstract module SlidingWindow {

    //Type we will fix in the concrete module
    type T
    
    /** Predicate that allow us to check if the property holds in the
    *   defined by the v : seq<T>uence and its limits [ini, fin)
    * 
    *   v -> [ * | * | ... |  *   ] 
    *         ini| ...     |fin-1| fin
    */
    ghost function is_true_on_segment(v : seq<T>, ini : int, fin : int) : bool
    requires 0 <= ini <= fin <= |v|

    /** Function used for keeping the cardinal of the segments that hold    
    *   the propoerty.
    */
    ghost function we_counted_rigth(v : seq<T>, r : int, l : int) : bool
    requires l >= 1
    {
        r == |valid_segments(v, 0, |v|, l)|
    }

    //Main functions

    /** This function returns the set of pairs [p, fin) such that
    *   the property is true. 
    */
    ghost function valid_segments_fixed_last(v : seq<T>, ini : int, fin : int, l : int) : set<(int, int)>
    requires 0 <= ini <= fin <= |v| 
    requires l >= 1
    {   
        if(fin - l >= ini && is_true_on_segment(v, fin - l, fin)) then {(fin - l, fin)}
        else {}
    }


    /** This function returns the set of pairs [p, q) such that
    *   the property is true.
    */
    ghost function valid_segments(v : seq<T>, ini : int, fin : int, l : int) : set<(int, int)>
    requires 0 <= ini <= fin <= |v|
    requires l >= 1
    {
        if(ini == fin) then {}
        else valid_segments(v, ini, fin - 1, l) + valid_segments_fixed_last(v, ini, fin, l)
    }

    /** This function returns the least index, k such that
    *   the property is true in the segment [k, fin)
    */
    ghost function min_pos_val(v : seq<T>, ini : int, fin : int) : int
    requires 0 <= ini <= fin <= |v|

    //Methods


    /** Used to give the variables apropiate values to enter the main loop
    */
    method variable_initialization(v : array<T>, l : int) returns (r : int, k : int, n : int)
    requires 1 <= l <= v.Length
    ensures 0 <= k <= n <= v.Length
    ensures r == |valid_segments(v[..], 0, n, l)| 
    ensures k == min_pos_val(v[..], 0, n)

    /** Used to update the value of k when the value of n is increased */
    method update_seg_count(v : array<T>, r : int, old_limit : int, k : int, l : int) returns (new_r : int)
    requires 0 <= old_limit < v.Length
    requires l >= 1
    requires k == min_pos_val(v[..], 0, old_limit + 1)
    requires r == |valid_segments(v[..], 0, old_limit, l)|
    ensures new_r == |valid_segments(v[..], 0, old_limit + 1, l)|

    /** Used to update the value of r when the value of n is increased */
    method update_lower_limit(v : array<T>, ini : int, old_lw : int, new_up : int) returns (new_lw : int)
    requires 0 <= ini <= old_lw < new_up <= v.Length
    requires old_lw == min_pos_val(v[..], ini, new_up - 1)
    ensures 0 <= new_lw <= new_up
    ensures new_lw == min_pos_val(v[..], ini, new_up)

    /** Main mehthod */
    method mcount_seg(v : array<T>, l : int) returns (r : int)
    requires 1 <= l <= v.Length
    ensures we_counted_rigth(v[..], r, l)

    /** Lemma used to ensure that we can express our postcondition in a easier way */
    lemma valid_segments_snd(v : seq<T>, ini : int, fin : int, l : int)
    requires 0 <= ini <= fin <= |v|
    requires l >= 1
    ensures valid_segments(v, ini, fin, l) ==  set p | ini <= p - l < p <= fin && is_true_on_segment(v, p - l, p) :: (p - l, p)

}
