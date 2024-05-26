include "sliding_window.dfy"

/** This module refines sliding_window.dfy
*   if you want to know more about the functions
*   and methods explained here, please visit that module.
*/
abstract module SlidingWindowForAllP refines SlidingWindow{


    ghost function is_true_on_elem(elem : T) : bool
     
    ghost function is_true_on_segment(v : seq<T>, ini : int, fin : int) : bool
    {
        forall p | ini <= p < fin :: is_true_on_elem(v[p])
    }

    ghost function min_pos_val(v : seq<T>, ini : int, fin : int) : int
    {
        if(ini == fin) then ini
        else if(!is_true_on_elem(v[fin - 1])) then fin
        else min_pos_val(v, ini, fin - 1)
    }

    //Methods
    method m_is_true_elem(elem : T) returns (res : bool)
    ensures res == is_true_on_elem(elem)


    method variable_initialization(v : array<T>, l : int) returns (r : int, k : int, n : int)
    {
        n := l;
        valid_segments_shorter_than_l(v[..], 0, n - 1, l);

        r := 0; k := 0;
        
        var cond, aux, i := true, true, 0;

        while i < n
        invariant k <= i <= n
        invariant cond == is_true_on_segment(v[..], 0, i)
        invariant k == min_pos_val(v[..], 0, i)
        {
            aux := m_is_true_elem(v[i]);
            cond := cond && aux;

            if(!aux) {  k := i + 1; }

            i := i + 1;
        }

        if(cond) {  r := 1; }
    }

    method update_seg_count(v : array<T>, r : int, old_limit : int, k : int, l : int) returns (new_r : int)
    {
        var new_limit := old_limit + 1;
        new_r := r;

        min_pos_val_limits(v[..], 0, new_limit);
        min_pos_val_snd(v[..], 0, new_limit);
        no_need_to_come_back(v[..], 0, new_limit);
        
        if(new_limit - l >= 0){
            var cond :=  k <= new_limit - l;
            if (cond) { 
                new_r := r + 1;
                valid_segments_second(v[..], 0, old_limit, l);
            }
        }        
    }

    method update_lower_limit(v : array<T>, ini : int, old_lw : int, new_up : int) returns (new_lw : int)
    {
        new_lw := old_lw;
        if(new_up > 0) {
            var cond := m_is_true_elem(v[new_up - 1]);
            if(!cond) {  new_lw := new_up; }
        }
    }

    method mcount_seg(v : array<T>, l : int) returns (r : int)
    {
        var n : int, k : int;
        r, k, n := variable_initialization(v, l);

        while n < v.Length
        invariant 0 <= k <= n <= v.Length
        invariant k == min_pos_val(v[..], 0, n)   
        invariant r == |valid_segments(v[..], 0, n, l)|
        {
            min_pos_val_snd(v[..], 0, n + 1);

            k := update_lower_limit(v, 0, k, n + 1);
            
            r := update_seg_count(v, r, n, k, l); 

            n := n + 1;
        }
    }

    lemma valid_segments_second(v : seq<T>, ini : int, fin : int, l : int)
    requires 0 <= ini <= fin < |v|
    requires l >= 1
    ensures forall p, q | (p, q) in valid_segments(v, ini, fin, l) :: q <= fin
    {}

    lemma valid_segments_fixed_last_shorter_than_l(v : seq<T>, ini : int, fin : int, l : int)
    requires 0 <= ini <= fin <= |v| 
    requires l >= 1  && (fin - l) < ini 
    ensures valid_segments_fixed_last(v, ini, fin, l) == {}
    {}

    lemma valid_segments_shorter_than_l(v : seq<T>, ini : int, fin : int, l : int)
    requires 0 <= ini <= fin <= |v|
    requires l >= 1 && (fin - ini) < l
    ensures valid_segments(v, ini, fin, l) == {}
    {
        if(ini == fin){}
        else{
            valid_segments_shorter_than_l(v, ini, fin - 1, l);
            valid_segments_fixed_last_shorter_than_l(v, ini, fin, l);
            assert valid_segments_fixed_last(v, ini, fin, l) == {};
        }
    }

    lemma valid_segments_snd(v : seq<T>, ini : int, fin : int, l : int)
    {}

    lemma min_pos_val_limits(v : seq<T>, ini : int, fin : int)
    requires 0 <= ini <= fin <= |v|
    ensures ini <= min_pos_val(v, ini, fin) <= fin
    {}

    lemma min_pos_val_snd(v : seq<T>, ini : int, fin : int)
    requires 0 <= ini <= fin <= |v|
    requires ini <= min_pos_val(v, ini, fin) <= fin
    ensures is_true_on_segment(v, min_pos_val(v, ini, fin), fin)
    {
        if(ini < fin && is_true_on_elem(v[fin - 1])){
            min_pos_val_limits(v, ini, fin - 1);
            min_pos_val_snd(v, ini, fin - 1);
        }
    }

    lemma closed_on_left_lemma()
    ensures forall ini, fin, p, s : seq<T> | 0 <= ini <= p <= fin <= |s| && is_true_on_segment(s,ini,fin) :: is_true_on_segment(s,ini,p)
    {}

    lemma no_need_to_come_back(s : seq<T>, ini : int, fin : int)
    requires 0 <= ini <= fin <= |s|
    ensures forall p : int | ini <= p < min_pos_val(s, ini, fin) <= fin :: !is_true_on_segment(s, p, fin)
    {
        if (ini + 1 < fin) {
            if(is_true_on_elem(s[fin - 1])){
                //Hipótesis de inducción
                no_need_to_come_back(s, ini, fin - 1);
                
                var border := min_pos_val(s, ini, fin - 1);

                if(exists p | ini <= p < border <= fin :: is_true_on_segment(s, p, fin)){
                    
                    closed_on_left_lemma();
                    min_pos_val_limits(s, ini, fin - 1);

                    assert is_true_on_segment(s, border - 1, fin - 1);

                    assert false;
                }
            }
        }
    }}