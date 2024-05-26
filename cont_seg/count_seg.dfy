
/** This module represents the abstract methods that are required to
*   solve in an iterative way a problem that tries to find the number
*   of segments that fulfills a property over a vector.
*/

abstract module ContSeg {

    //Type that we will fix later
    type T

    //Functions

    ghost function is_true_on_segment(v : seq<T>, ini : int, fin : int) : bool
    requires 0 <= ini <= fin <= |v|

    /** Function used for keeping the cardinal of the segments that hold    
    *   the propoerty.
    */
    ghost function we_counted_rigth(v : seq<T>, r : int) : bool
    {
        r == |valid_segments(v, 0, |v|)|
    }

    /** This function returns the set of pairs [p, fin) such that
    *   the property is true. 
    */
    ghost function valid_segments_fixed_last(v : seq<T>, ini : int, fin : int) : set<(int, int)>
    requires 0 <= ini <= fin <= |v|
    {
        set p | ini <= p < fin && is_true_on_segment(v, p, fin) :: (p, fin)
    }

    /** This function returns the set of pairs [p, q) such that
    *   the property is true.
    */
    ghost function valid_segments(v : seq<T>, ini : int, fin : int) : set<(int, int)>
    requires 0 <= ini <= fin <= |v|
    {
        if(ini == fin) then {}
        else valid_segments(v, ini, fin - 1) + valid_segments_fixed_last(v, ini, fin)
    }

    /** This function returns the least index, k such that
    *   the property is true in the segment [k, fin)
    */
    ghost function min_pos_val(v : seq<T>, ini : int, fin : int) : int
    requires 0 <= ini <= fin <= |v|

    //Métodos

    /** Used to give the variables apropiate values to enter the main loop
    */
    method variable_initialization(v : array<T>) returns (r : int, k : int, n : int)
    ensures 0 <= k <= n <= v.Length
    ensures r == |valid_segments(v[..], 0, n)| 
    ensures k == min_pos_val(v[..], 0, n)

    /** Used to update the value of k when the value of n is increased */
    method update_lower_limit(v : array<T>, ini : int, old_lw : int, new_up : int) returns (new_lw : int)
    requires 0 <= ini <= old_lw < new_up <= v.Length
    requires old_lw == min_pos_val(v[..], ini, new_up - 1)
    ensures 0 <= new_lw <= new_up
    ensures new_lw == min_pos_val(v[..], ini, new_up)

    /** Used to update the value of r when the value of n is increased */
    method update_seg_count(v : array<T>, r : int, new_lw : int, old_up : int) returns (new_r : int)
    requires 0 <= new_lw <= old_up + 1 <= v.Length 
    requires 0 <= old_up < v.Length
    requires new_lw == min_pos_val(v[..], 0, old_up + 1)
    requires r == |valid_segments(v[..], 0, old_up)|
    ensures new_r == |valid_segments(v[..], 0, old_up + 1)|

    /** Main mehthod */
    method mcount_seg(v : array<T>) returns (r : int)
    ensures we_counted_rigth(v[..], r)

    /** Lemma used to ensure that we can express our postcondition in a easier way */
    lemma valid_segments_snd(v : seq<T>, ini : int, fin : int)
    requires 0 <= ini <= fin <= |v|
    ensures valid_segments(v, ini, fin) ==  (set p, q | ini <= p < q <= fin && is_true_on_segment(v, p, q) :: (p, q))

}