include "../abstract_closed_left.dfy"

/** This module describe and model properties of the type:
*       "Forall elements of the segment R(x, y)"
*   we define this kind of properties and prove the lemmas
*   needed to implement an eficient method that solves the problem 
*   of finding the longest segment over a vector given an 
*   relation property that is transitive.
*/
module SegLongMaxRelation refines AbstractClosedLeft {
        
    /** Relation to be defined by the user */
    ghost function is_true_relation(elem1 : T, elem2 : T) : bool

    /** The property is true in the segment if the defined relation is true
    *   between all the elements of the segment.
    */
    ghost function is_true_on_segment(v : seq<T>, ini : int, fin : int) : bool
    {
        forall p, q | ini <= p < q < fin :: is_true_relation (v[p], v[q])
    }

    /** Predicate that models what it means for Q to compose its segments. */
    ghost predicate composes_segments(v : seq<T>, ini : int, fin : int)
    requires 0 <= ini <= fin <= |v|
    {
        forall i, j, k | ini <= i < j < k <= fin :: is_true_on_segment(v, i, j + 1) && is_true_on_segment(v, j, k) ==> is_true_on_segment(v, i, k)
    }

    /** Very similar function to the one defined in the unitary module */
    ghost function seg_long_max(v : seq<T>, ini : int, fin : int) : (int, int)
    {
        if(ini == fin) then (0, ini)
        //We distinguish  the case when the segment only has one element, which is 
        // trivially true.
        else if(ini + 1 == fin) then (1, ini)
        //When the property is not true, we update the lower bound to the actual last element of the segment.
        else if (!is_true_relation(v[fin - 2], v[fin - 1])) then (seg_long_max(v, ini, fin - 1).0, fin - 1)
        //If the property is true, we compere the actual length of the segment with the actual max and
        // we return the previous lower bound.
        else (max(seg_long_max(v, ini, fin - 1).0, fin - seg_long_max(v, ini, fin - 1).1), seg_long_max(v, ini, fin - 1).1)
    }

    //Methods 

    /** Method that implements the property defined before */
    method m_true_relation(elem1 : T, elem2 : T) returns (res : bool)
    ensures res == is_true_relation(elem1, elem2)

    //Methods already described in the abstract module
    method variable_initialization(v : array<T>) returns (r : int, s : int, n : int)
    {
        r, s, n := 0, 0, 0;
    }

    method update_actual_s(v : array<T>, ini : int, old_s : int, new_n : int) returns (new_s : int)
    {
        new_s := old_s;
        if(new_n - old_s) > 1 {
            var res := m_true_relation(v[new_n - 2], v[new_n - 1]);
            if !res { new_s := new_n - 1; }
        } 
    }

    method update_actual_seg_length(v : array<T>, old_r : int, old_n : int, new_s : int) returns (new_r : int)
    {
        new_r := mmax(old_r, old_n + 1 - new_s);
        
        if(old_n > 0){
            seg_long_max_gt_1(v[..], 0, old_n);
        }
    }

    /** Lemma that ensures that our property composes segments, to be proved by the user.*/
    lemma it_composes_segments(s : seq<T>)
    ensures forall ini : int, fin : int | 0 <= ini < fin <= |s| :: composes_segments(s, ini, fin)

    //Lemas described in the abstract module
    lemma allways_gt(s : seq<T>, fin : int)
    {
        if(fin > 1){   seg_long_max_gt_1(s, 0, fin);  }
    }

    lemma seg_long_max_gt(s : seq<T>, ini : int, fin : int)
    {}

    lemma seg_long_max_gt_1(s : seq<T>, ini : int, fin : int)
    requires 0 <= ini < fin <= |s|
    ensures seg_long_max(s, ini, fin).0 >= 1
    {}

    lemma upper_limit(s : seq<T>, ini : int, fin : int)
    {}

    lemma closed_on_left_lemma()
    {}

    lemma no_need_to_come_back(s : seq<T>, ini : int, fin : int)
    {
        if (ini + 1 < fin) {
            if(is_true_relation(s[fin - 2], s[fin - 1])){
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


    lemma seg_long_max_snd(v : seq<T>, ini : int, fin : int)
    {
        if(ini + 1 < fin ){
            if(is_true_relation(v[fin - 2], v[fin - 1])){
                //Sabemos que existe un segmento que lo cumple.
                seg_long_max_existence(v, ini, fin - 1);
                //No hace falta mirar los que son más pequeños que el que traíamos
                no_need_to_come_back(v, ini, fin);
            } else if (!is_true_relation(v[fin - 2], v[fin - 1])){
                //Basta con ver que es mayor o igual que cero
                seg_long_max_gt_1(v, ini, fin);
            }
        }
    }

    lemma seg_long_max_existence(v : seq<T>, ini : int, fin : int)
    {
        //Caso base
        if(ini == fin){
            assert is_true_on_segment(v, ini, fin);
        }
        //Segmento de un elemento 
        else if (ini + 1 == fin){
            assert is_true_on_segment(v, ini, ini);
            assert is_true_on_segment(v, ini, fin);
        }
        //Caso en que el último elemento no cumple
        else if (!is_true_relation(v[fin - 2], v[fin - 1])){
            assert is_true_on_segment(v, fin - 1, fin);   
            seg_long_max_existence(v, ini, fin - 1);  
        }
        else {
            //Hipótesis de inducción
            seg_long_max_existence(v, ini, fin - 1);

            //Demostramos que para el segmento completo se cumple
            var border := seg_long_max(v, ini, fin).1;

            it_composes_segments(v);
            assert composes_segments(v, border, fin);

            assert is_true_on_segment(v, border, fin - 1);
            assert is_true_on_segment(v, fin - 2, fin);
        } 
    }
    
}


