abstract module SlidingWindow {

    type T
    
    /** Predicate that allow us to check if the property holds in the
    *   defined by the v : seq<T>uence and its limits [ini, fin)
    * 
    *   v -> [ * | * | ... |  *   ] 
    *         ini| ...     |fin-1| fin
    */
    ghost function is_true_on_segment(v : seq<T>, ini : int, fin : int) : bool
    requires 0 <= ini <= fin <= |v|

    ghost function we_counted_rigth(v : seq<T>, r : int, l : int) : bool
    requires l >= 1
    {
        r == |valid_segments(v, 0, |v|, l)|
    }

    //Funciones
    ghost function valid_segments_fixed_last(v : seq<T>, ini : int, fin : int, l : int) : set<(int, int)>
    requires 0 <= ini <= fin <= |v| 
    requires l >= 1
    {   
        if(fin - l >= ini && is_true_on_segment(v, fin - l, fin)) then {(fin - l, fin)}
        else {}
    }

    ghost function valid_segments(v : seq<T>, ini : int, fin : int, l : int) : set<(int, int)>
    requires 0 <= ini <= fin <= |v|
    requires l >= 1
    {
        if(ini == fin) then {}
        else valid_segments(v, ini, fin - 1, l) + valid_segments_fixed_last(v, ini, fin, l)
    }


    ghost function min_pos_val(v : seq<T>, ini : int, fin : int) : int
    requires 0 <= ini <= fin <= |v|

    //Métodos

    method variable_initialization(v : array<T>, l : int) returns (r : int, k : int, n : int)
    requires 1 <= l <= v.Length
    ensures 0 <= k <= n <= v.Length
    ensures r == |valid_segments(v[..], 0, n, l)| 
    ensures k == min_pos_val(v[..], 0, n)


    method update_seg_count(v : array<T>, r : int, old_limit : int, k : int, l : int) returns (new_r : int)
    requires 0 <= old_limit < v.Length
    requires l >= 1
    requires k == min_pos_val(v[..], 0, old_limit + 1)
    requires r == |valid_segments(v[..], 0, old_limit, l)|
    ensures new_r == |valid_segments(v[..], 0, old_limit + 1, l)|

    method update_lower_limit(v : array<T>, ini : int, old_lw : int, new_up : int) returns (new_lw : int)
    requires 0 <= ini <= old_lw < new_up <= v.Length
    requires old_lw == min_pos_val(v[..], ini, new_up - 1)
    ensures 0 <= new_lw <= new_up
    ensures new_lw == min_pos_val(v[..], ini, new_up)


    method mcount_seg(v : array<T>, l : int) returns (r : int)
    requires 1 <= l <= v.Length
    ensures we_counted_rigth(v[..], r, l)

    lemma valid_segments_snd(v : seq<T>, ini : int, fin : int, l : int)
    requires 0 <= ini <= fin <= |v|
    requires l >= 1
    ensures valid_segments(v, ini, fin, l) ==  set p | ini <= p - l < p <= fin && is_true_on_segment(v, p - l, p) :: (p - l, p)

}
