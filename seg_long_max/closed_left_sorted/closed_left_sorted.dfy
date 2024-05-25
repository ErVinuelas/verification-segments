include "../basics.dfy"


/** This module represents properties that are closed on the left
*   and also true on the void segment. The functions are explained in
*   the /general/seg_long_max_abs.dfy file.
*/ 
module SegLongMaxClosedLeftSorted {
    import opened BasicFunctions
    import opened BasicMethods

    type T = int

    ghost function is_true_on_segment(v : seq<T>, ini : int, fin : int) : (bool)
    requires 0 <= ini <= fin <= |v|
    
    ghost predicate is_longest_segment(s : seq<T>, r : int)
    {   
        forall p : int, q : int | 0 <= p <= q <= |s| && is_true_on_segment(s, p, q) :: q - p <= r
    }

    ghost predicate there_is_a_segment_that_long(s : seq<T>, r : int)
    {
        exists p : int, q : int | 0 <= p <= q <= |s| && is_true_on_segment(s, p, q) :: q - p == r
    }

    /** Predicate that ensures that the sequence we are studiying is ordered 
    */
    ghost predicate sorted(s : seq<T>)
    {
        forall p : int, q : int | 0 <= p <= q < |s| :: s[p] <= s[q]
    }

    /** This function is used to model the update the lower bound of a segment. 
    */
    ghost function update_s(v : seq<T>, ini : int, fin : int) : (int)
    decreases fin - ini
    requires 0 <= ini <= fin <= |v|
    {
        if(ini == fin) then ini
        else if(is_true_on_segment(v, ini, fin)) then ini
        else update_s(v, ini + 1, fin)
    }

    ghost function seg_long_max(v : seq<T>, ini : int, fin : int) : (int, int)
    requires 0 <= ini <= fin <= |v|
    {
        if(ini == fin) then (0, ini)
        else if (!is_true_on_segment(v, ini, fin)) then (max(seg_long_max(v, ini, fin - 1).0, fin - update_s(v, ini, fin)), update_s(v, ini, fin))
        else (max(seg_long_max(v, ini, fin - 1).0, fin - seg_long_max(v, ini, fin - 1).1), seg_long_max(v, ini, fin - 1).1)
    }

    //New Lemmas

    /** Used to ensure that the value returned by "update_s" is 
    *   suitable as a lower bound for the segment
    */
    lemma update_s_good_segment(v : seq<T>, ini : int, fin : int)
    decreases fin - ini
    requires 0 <= ini <= fin <= |v|
    requires ini <= update_s(v, ini, fin) <= fin
    ensures is_true_on_segment(v, update_s(v, ini, fin), fin)
    {
        if(ini == fin) {    prop_is_true_on_void(v); }
        else if(!is_true_on_segment(v, ini, fin)){
            update_s_limits(v, ini + 1, fin);
            update_s_good_segment(v, ini + 1, fin);
        }
    }

    lemma update_s_is_seg_long_1(v : seq<T>, ini : int, fin : int)
    decreases fin - ini
    requires 0 <= ini <= fin <= |v|
    requires sorted(v)
    ensures seg_long_max(v, ini, fin).1 == update_s(v, ini, fin)
    {
        if(ini < fin && is_true_on_segment(v, ini, fin)){
            seg_long_max_1_is_ini(v, ini, fin);
        }
    }

    lemma update_s_min_value(v : seq<T>, ini : int, fin : int)
    decreases fin - ini
    requires 0 <= ini <= fin <= |v|
    ensures forall p | ini <= p <= fin && is_true_on_segment(v, p, fin) :: update_s(v, ini, fin) <= p
    {        
        if(ini < fin && !is_true_on_segment(v, ini, fin)){
            update_s_min_value(v, ini + 1, fin);
        }
    }

    lemma update_s_limits(v : seq<T>, ini : int, fin : int)
    decreases fin - ini
    requires 0 <= ini <= fin <= |v|
    ensures ini <= update_s(v, ini, fin) <= fin
    {
        if(ini < fin && !is_true_on_segment(v, ini, fin)){
            update_s_limits(v, ini + 1, fin);
        }
    }

    lemma seg_long_max_1_is_ini(v : seq<T>, ini : int, fin : int)
    requires 0 <= ini <= fin <= |v|
    requires sorted(v)
    requires is_true_on_segment(v, ini, fin)
    ensures seg_long_max(v, ini, fin).1 == ini
    {
        if(ini < fin) { 
            closed_on_left_lemma(v);
            seg_long_max_1_is_ini(v, ini, fin - 1); 
        }   
    }    
    
    lemma update_s_if_snd(v : seq<T>, ini : int, old_s : int, fin : int)
    requires 0 <= ini < fin <= |v|
    requires sorted(v)
    requires ini <= old_s <= fin
    requires old_s == update_s(v, ini, fin - 1)
    ensures update_s(v, ini, fin) == update_s(v, old_s, fin)
    {
        update_s_min_value(v, ini, fin - 1);

        if(update_s(v, ini, fin) < update_s(v, old_s, fin)){
            
            var p := update_s(v, ini, fin);
            var new_s := update_s(v, old_s, fin);

            update_s_limits(v, ini, fin);
            update_s_good_segment(v, ini, fin);

            assert is_true_on_segment(v, p, fin);

            closed_on_left_lemma(v);
            
            if(p < old_s){
                assert is_true_on_segment(v, p, fin - 1);
                assert false;
            } else {
                update_s_min_value(v, old_s, fin);

                assert p >= update_s(v, old_s, fin);
            }
        } else if(update_s(v, ini, fin) > update_s(v, old_s, fin)){
            update_s_min_value(v, ini, fin);
            update_s_limits(v, old_s, fin);
            update_s_good_segment(v, old_s, fin);

            assert false;
        }
    }
    
    method m_true_on_segment(v : array<T>, ini : int, fin : int) returns (res : bool)
    requires 0 <= ini <= fin <= v.Length
    ensures res == is_true_on_segment(v[..], ini, fin)


    method variable_initialization(v : array<T>) returns (r : int, s : int, n : int)
    ensures 0 <= s <= n <= v.Length
    ensures r == seg_long_max(v[..], 0, n).0 
    ensures s == seg_long_max(v[..], 0, n).1
    {
        r, s, n := 0, 0, 0;
    }

    method update_actual_s(v : array<T>, ini : int, old_s : int, new_n : int) returns (new_s : int)
    requires 0 <= ini <= old_s < new_n <= v.Length
    requires sorted(v[..])
    requires old_s == seg_long_max(v[..], ini, new_n - 1).1
    ensures 0 <= new_s <= new_n
    ensures new_s == seg_long_max(v[..], ini, new_n).1
    {
        new_s := old_s;

        update_s_limits(v[..], old_s, new_n);
        var cond := m_true_on_segment(v, new_s, new_n);

        while(!cond)
        decreases new_n - new_s
        invariant new_s <= update_s(v[..], old_s, new_n)
        invariant cond == is_true_on_segment(v[..], new_s, new_n)
        {
            update_s_good_segment(v[..], old_s, new_n);
        
            new_s := new_s + 1;

            cond := m_true_on_segment(v, new_s, new_n);
        }

        update_s_min_value(v[..], ini, new_n);
        update_s_is_seg_long_1(v[..], ini, new_n - 1);
        assert is_true_on_segment(v[..], new_s, new_n);        
        update_s_if_snd(v[..], ini, old_s, new_n);
    }

    method update_actual_seg_length(v : array<T>, old_r : int, old_n : int, new_s : int) returns (new_r : int)
    requires 0 <= old_n < v.Length
    requires old_r == seg_long_max(v[..], 0, old_n).0
    requires new_s == seg_long_max(v[..], 0, old_n + 1).1
    ensures new_r == seg_long_max(v[..], 0, old_n + 1).0
    {
        seg_long_max_gt(v[..], 0, old_n);

        new_r := mmax(old_r, old_n + 1 - new_s);
    }
    
    method mseg_long_max(v : array<T>) returns (r : int)
    requires sorted(v[..])
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
                allways_gt(v[..], n);
                //Forma de actualizar
                s := update_actual_s(v, 0, s, n + 1);

                r := update_actual_seg_length(v, r, n, s);

                n := n + 1;
            }

            //Lemas que prueban las post-condiciones
            seg_long_max_existence(v[..], 0, v.Length);
            seg_long_max_snd(v[..], 0, v.Length);
    }


    lemma allways_gt(s : seq<T>, fin : int)
    requires 0 <= fin <= |s|
    requires sorted(s)
    ensures seg_long_max(s, 0, fin).0 >= fin - seg_long_max(s, 0, fin).1
    {
        if(fin != 0 && !is_true_on_segment(s, 0, fin)){
            seg_long_max_snd(s, 0, fin);
        }
    }

    lemma upper_limit(s : seq<T>, ini : int, fin : int)
    requires 0 <= ini < fin <= |s|
    ensures seg_long_max(s, ini, fin).1 <= fin
    {
        update_s_limits(s, ini, fin);
    }

    lemma no_need_to_come_back(s : seq<T>, ini : int, fin : int)
    requires 0 <= ini < fin <= |s|
    requires sorted(s)
    ensures forall p : int | ini <= p < seg_long_max(s, ini, fin).1 <= fin :: !is_true_on_segment(s, p, fin)
    {
        if (ini + 1 < fin) {
            if(is_true_on_segment(s, ini, fin)){
                //Hipótesis de inducción
                no_need_to_come_back(s, ini, fin - 1);
                
                var border := seg_long_max(s, ini, fin - 1).1;
                       
                if(exists p | ini <= p < border <= fin :: is_true_on_segment(s, p, fin)){
                    closed_on_left_lemma(s);
                    upper_limit(s, ini, fin - 1);

                    var p :| ini <= p < border <= fin && is_true_on_segment(s, p, fin);

                    assert is_true_on_segment(s, p, fin - 1);

                    assert false;
                }
            } else if(!is_true_on_segment(s, ini, fin)){
                update_s_min_value(s, ini, fin);
            }
        }
    }

    lemma seg_long_max_gt(s : seq<T>, ini : int, fin : int)
    requires 0 <= ini <= fin <= |s| //Estaba estricto antes
    ensures seg_long_max(s, ini, fin).0 >= 0
    {}

    lemma seg_long_max_snd(v : seq<T>, ini : int, fin : int)
    requires 0 <= ini <= fin <= |v|
    requires sorted(v)
    ensures forall p, q | ini <= p <= q <= fin && is_true_on_segment(v, p, q) :: q - p <= seg_long_max(v, ini, fin).0
    {
        if(ini + 1 < fin ){
            if(is_true_on_segment(v, ini, fin)){
                //Sabemos que existe un segmento que lo cumple.
                seg_long_max_existence(v, ini, fin - 1);
                //No hace falta mirar los que son más pequeños que el que traíamos
                no_need_to_come_back(v, ini, fin);
            } else if (!is_true_on_segment(v, ini, fin)){
                update_s_min_value(v, ini, fin);
            }
        }
    }

    lemma seg_long_max_existence(v : seq<T>, ini : int, fin : int)
    requires 0 <= ini <= fin <= |v|    
    requires sorted(v)
    ensures exists p, q | ini <= p <= q <= fin && is_true_on_segment(v, p, q) :: q - p == seg_long_max(v, ini, fin).0
    ensures exists p | ini <= p <= fin && is_true_on_segment(v, p, fin) :: p == seg_long_max(v, ini, fin).1
    {
        //Caso base
        if(ini == fin){
            prop_is_true_on_void(v);
            assert is_true_on_segment(v, ini, fin);
        }
        //Caso en que el último elemento cumple
        else if (!is_true_on_segment(v, ini, fin)){
            seg_long_max_existence(v, ini, fin - 1);
            update_s_limits(v, ini, fin);

            var new_border := update_s(v, ini, fin);
            assert new_border == seg_long_max(v, ini, fin).1;

            update_s_good_segment(v, ini, fin);

            assert is_true_on_segment(v, new_border, fin);
        }
        else {
            //Hipótesis de inducción
            seg_long_max_existence(v, ini, fin - 1);
            assert is_true_on_segment(v, ini, fin);
            //Demostramos que para el segmento completo se cumple
            var border := seg_long_max(v, ini, fin).1;
            no_need_to_come_back(v, ini, fin);

            assert is_true_on_segment(v, border, fin);
        }  
    }

    //Se deja al usuario
    lemma closed_on_left_lemma(s : seq<T>)
    requires sorted(s)
    ensures forall ini, fin, p| 0 <= ini <= p <= fin <= |s| && is_true_on_segment(s,ini,fin) :: is_true_on_segment(s,ini,p)

    
    /** Ensures that the property is true for the void segment. */
    lemma prop_is_true_on_void(v : seq<T>)
    ensures forall p | 0 <= p <= |v| :: is_true_on_segment(v, p, p)
}

