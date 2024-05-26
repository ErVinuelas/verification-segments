include "../abstract_closed_left.dfy"

/** This module describes and model properties of the type:
*       "Forall elements of the segment P(x) is true"
*   we define this kind of properties and prove the lemmas
*   needed to implement the method that solves the problem 
*   of finding the longest segment over a vector given an 
*   unary property.
*/
abstract module SegLongMaxUnitary refines AbstractClosedLeft {

    /** Property that needs to be fulfilled for all the elements
  *    of the segment.
    */
    ghost function is_true_on_elem(elem : T) : bool

    /** A segment is considered to fulfill the property if all its elements
    *   hold the property the user will define.
    */
    ghost function is_true_on_segment(v : seq<T>, ini : int, fin : int) : bool
    {
        forall p | ini <= p < fin :: is_true_on_elem(v[p])
    }

    ghost function seg_long_max(v : seq<T>, ini : int, fin : int) : (int, int)
    {
        //The lenght of [ini, ini) is 0 and since forall is true on void its a valid segment
        if(ini == fin) then (0, ini)
        //If the property is not true on the last element, it is not true on the whole segment
        //that contains it. Therefore, we take the previous max and restart the lower boudn.
        else if (!is_true_on_elem(v[fin - 1])) then (seg_long_max(v, ini, fin - 1).0, fin)
        //Is the property holds, them we compare the length of the actual segment with the actual max
        // and update it. We also return the actual lower bound.
        else (max(seg_long_max(v, ini, fin - 1).0, fin - seg_long_max(v, ini, fin - 1).1), seg_long_max(v, ini, fin - 1).1)
    }

    /** This method represents the property that our program will
    *    check.
    */
    method m_true_on_elem(elem : T) returns (res : bool)
    ensures res == is_true_on_elem(elem)

    //Methods defined in the abstract module
    method variable_initialization(v : array<T>) returns (r : int, s : int, n : int)
    {
        r, s, n := 0, 0, 0;
    }

    method update_actual_s(v : array<T>, ini : int, old_s : int, new_n : int) returns (new_s : int)
    {
        var res := m_true_on_elem(v[new_n - 1]);
        if (new_n > 0 && !res) { new_s := new_n; } 
        else {  new_s := old_s; }
    }

    method update_actual_seg_length(v : array<T>, old_r : int, old_n : int, new_s : int) returns (new_r : int)
    {
        seg_long_max_gt(v[..], 0, old_n);
        new_r := mmax(old_r, old_n + 1 - new_s);
    }

    //Lemas defined and described on the abstract module
    lemma allways_gt(s : seq<T>, fin : int)
    {
        if(fin != 0){   seg_long_max_gt(s, 0, fin);  }
    }

    lemma closed_on_left_lemma()
    {}

    lemma upper_limit(s : seq<T>, ini : int, fin : int)
    {}

    lemma no_need_to_come_back(s : seq<T>, ini : int, fin : int)
    {
        if (ini + 1 < fin) {
            if(is_true_on_elem(s[fin - 1])){
                //Hipótesis de inducción
                no_need_to_come_back(s, ini, fin - 1);
                
                var border := seg_long_max(s, ini, fin - 1).1;

                if(exists p | ini <= p < border <= fin :: is_true_on_segment(s, p, fin)){
                    
                    closed_on_left_lemma();
                    upper_limit(s, ini, fin - 1);

                    assert is_true_on_segment(s, border - 1, fin - 1);

                    assert false;
                }
            }
        }
    }

    lemma seg_long_max_gt(s : seq<T>, ini : int, fin : int)
    {}

    lemma seg_long_max_snd(v : seq<T>, ini : int, fin : int)
    {
        if(ini + 1 < fin ){
            if(is_true_on_elem(v[fin - 1])){
                //Sabemos que existe un segmento que lo cumple.
                seg_long_max_existence(v, ini, fin - 1);
                //No hace falta mirar los que son más pequeños que el que traíamos
                no_need_to_come_back(v, ini, fin);
            } else {
                //Basta con ver que es mayor o igual que cero
                seg_long_max_gt(v, ini, fin);
            }
        }
    }

    lemma seg_long_max_existence(v : seq<T>, ini : int, fin : int)
    {
        //Caso base
        if(ini == fin){
            assert is_true_on_segment(v, ini, fin);
        }
        //Caso en que el último elemento cumple
        else if (!is_true_on_elem(v[fin - 1])){
            assert is_true_on_segment(v, fin, fin);   
            seg_long_max_existence(v, ini, fin - 1);  
        }
        else {
            //Hipótesis de inducción
            seg_long_max_existence(v, ini, fin -1);
            
            //Demostramos que para el segmento completo se cumple
            var border := seg_long_max(v, ini, fin).1;
            assert is_true_on_segment(v, border, fin);
        }  
    }

}