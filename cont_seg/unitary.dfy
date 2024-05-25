include "count_seg.dfy"

abstract module ContSegForAllP refines ContSeg {

    //Funciones
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

    //Métodos
    method m_is_true_elem(elem : T) returns (res : bool)
    ensures res == is_true_on_elem(elem)

    method variable_initialization(v : array<T>) returns (r : int, k : int, n : int)
    ensures 0 <= k <= n <= v.Length
    ensures r == |valid_segments(v[..], 0, n)| 
    ensures k == min_pos_val(v[..], 0, n)
    {
        r, k, n := 0, 0, 0;
    }

    method update_lower_limit(v : array<T>, ini : int, old_lw : int, new_up : int) returns (new_lw : int)
    {
        new_lw := old_lw;
        if(new_up > 0) {
            var cond := m_is_true_elem(v[new_up - 1]);
            if(!cond) {  new_lw := new_up; }
        }
    }

    method update_seg_count(v : array<T>, r : int, new_lw : int, old_up : int) returns (new_r : int)
    {        
        valid_segments_void_intersection(v[..], old_up);
        valid_segments_fixed_last_count(v[..], 0, old_up + 1);
        
        new_r := r + (old_up - new_lw + 1);
    }

    method mcount_seg(v : array<T>) returns (r : int)
    {
        var n : int, k : int;
        r, k, n := variable_initialization(v);

        while n < v.Length
        invariant 0 <= k <= n <= v.Length
        invariant k == min_pos_val(v[..], 0, n)
        invariant r == |valid_segments(v[..], 0, n)|   
        {
            min_pos_val_snd(v[..], 0, n + 1);

            k := update_lower_limit(v, 0, k, n + 1);

            r := update_seg_count(v, r, k, n); 

            n := n + 1;
        }
    }

    //Lemas

    lemma closed_on_left_lemma()
    ensures forall ini, fin, p, s : seq<T> | 0 <= ini <= p <= fin <= |s| && is_true_on_segment(s,ini,fin) :: is_true_on_segment(s,ini,p)
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
    }

    lemma count_pair_segment(ini : int, fin : int)
    decreases fin - ini
    requires ini <= fin
    ensures |set p | ini <= p < fin :: (p, fin)| == fin - ini
    {
        if(ini < fin){
            count_pair_segment(ini + 1, fin);
            assert (set p | ini <= p < fin :: (p, fin)) - (set p | (ini + 1) <= p < fin :: (p, fin)) == {(ini, fin)};
            assert |{(ini, fin)}| == 1;
        }
    }

    lemma valid_segments_fixed_last_count(v : seq<T>, ini : int, fin : int)
    decreases fin - ini
    requires 0 <= ini <= fin <= |v|
    ensures (fin - min_pos_val(v, ini, fin)) == |valid_segments_fixed_last(v, ini, fin)|
    {
        min_pos_val_limits(v, ini, fin);
        min_pos_val_snd(v, ini, fin);
        no_need_to_come_back(v, ini, fin);

        if(is_true_on_segment(v, ini, fin)){

            assert valid_segments_fixed_last(v, ini, fin) == (set p | ini <= p < fin :: (p, fin));
            
            count_pair_segment(ini, fin);
        }
        else{
            if(is_true_on_elem(v[fin - 1])){                
                var low := min_pos_val(v, ini, fin);

                min_pos_val_limits(v, low, fin);
                min_pos_val_snd(v, low, fin);
                no_need_to_come_back(v, low, fin);

                assert valid_segments_fixed_last(v, ini, fin) == valid_segments_fixed_last(v, low, fin);
            }
        }
    }

    lemma valid_segments_second(v : seq<T>, ini : int, fin : int)
    requires 0 <= ini <= fin < |v|
    ensures forall p, q | (p, q) in valid_segments(v, ini, fin) :: q <= fin
    {}

    lemma valid_segments_void_intersection(v : seq<T>, fin : int)
    requires 0 <= fin < |v|
    ensures valid_segments(v, 0, fin) * valid_segments_fixed_last(v, 0, fin + 1) == {}
    {
        if(fin > 0) {
            var fixed := valid_segments_fixed_last(v, 0, fin + 1);
            var not_fixed := valid_segments(v, 0, fin);
            if(exists p, q | 0 <= p < q <= |v| :: (p, q) in fixed && (p, q) in not_fixed){
                valid_segments_second(v, 0, fin);
                assert false;
            }
        }
    }

    lemma valid_segments_snd(v : seq<T>, ini : int, fin : int)
    ensures valid_segments(v, ini, fin) ==  (set p, q | ini <= p < q <= fin && is_true_on_segment(v, p, q) :: (p, q))
    {}
}