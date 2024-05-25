
abstract module ContSeg {

    type T

    //Functions

    ghost function is_true_on_segment(v : seq<T>, ini : int, fin : int) : bool
    requires 0 <= ini <= fin <= |v|

    ghost function we_counted_rigth(v : seq<T>, r : int) : bool
    {
        r == |valid_segments(v, 0, |v|)|
    }

    ghost function valid_segments_fixed_last(v : seq<T>, ini : int, fin : int) : set<(int, int)>
    requires 0 <= ini <= fin <= |v|
    {
        set p | ini <= p < fin && is_true_on_segment(v, p, fin) :: (p, fin)
    }

    ghost function valid_segments(v : seq<T>, ini : int, fin : int) : set<(int, int)>
    requires 0 <= ini <= fin <= |v|
    {
        if(ini == fin) then {}
        else valid_segments(v, ini, fin - 1) + valid_segments_fixed_last(v, ini, fin)
    }

    ghost function min_pos_val(v : seq<T>, ini : int, fin : int) : int
    requires 0 <= ini <= fin <= |v|

    //Métodos
    method variable_initialization(v : array<T>) returns (r : int, k : int, n : int)
    ensures 0 <= k <= n <= v.Length
    ensures r == |valid_segments(v[..], 0, n)| 
    ensures k == min_pos_val(v[..], 0, n)

    method update_lower_limit(v : array<T>, ini : int, old_lw : int, new_up : int) returns (new_lw : int)
    requires 0 <= ini <= old_lw < new_up <= v.Length
    requires old_lw == min_pos_val(v[..], ini, new_up - 1)
    ensures 0 <= new_lw <= new_up
    ensures new_lw == min_pos_val(v[..], ini, new_up)

    method update_seg_count(v : array<T>, r : int, new_lw : int, old_up : int) returns (new_r : int)
    requires 0 <= new_lw <= old_up + 1 <= v.Length 
    requires 0 <= old_up < v.Length
    requires new_lw == min_pos_val(v[..], 0, old_up + 1)
    requires r == |valid_segments(v[..], 0, old_up)|
    ensures new_r == |valid_segments(v[..], 0, old_up + 1)|

    method mcount_seg(v : array<T>) returns (r : int)
    ensures we_counted_rigth(v[..], r)

    lemma valid_segments_snd(v : seq<T>, ini : int, fin : int)
    requires 0 <= ini <= fin <= |v|
    ensures valid_segments(v, ini, fin) ==  (set p, q | ini <= p < q <= fin && is_true_on_segment(v, p, q) :: (p, q))

}