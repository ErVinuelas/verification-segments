include "../basics.dfy"

/** This module represents the abstract methods that are required to
*   solve in an iterative way a problem that tries to find the segment
*   of maximun length that fulfills a property over a vector.
*/

abstract module SegLongMax {
    import opened BasicMethods
    import opened BasicFunctions

    //Type we will be using, which we will fix in the final module
    type T

    /** Predicate that allow us to check if the property holds in the
    *   defined by the v : seq<T> and its limits [ini, fin)
    * 
    *   v -> [ * | * | ... |  *   ] 
    *         ini| ...     |fin-1| fin
    *
    *   In a segment of the form [p, q) we will refer to (p) as the
    *   "lower bound" and to (q) as the "upper bound". We say a segment
    *   [p, q) holds the property if "is_true_on_segment(v, p, q) == true"
    */
    ghost function is_true_on_segment(v : seq<T>, ini : int, fin : int) : bool
    requires 0 <= ini <= fin <= |v|

    /**
    *   Predicates that ensures that the integer (r) is the length of the longest
    *   segment over a vector. The predicate "is_longest_segment" requires that 
    *   such value must be greater or equal that any other that fulfills the 
    *   property. The predicate "there_is_a_segment_that_long" ensures that there
    *   is a segment that holds the property of such a length (r).
    */
    ghost function is_longest_segment(s : seq<T>, r : int) : bool
    {   
        forall p : int, q : int | 0 <= p <= q <= |s| && is_true_on_segment(s, p, q) :: q - p <= r
    }

    ghost function there_is_a_segment_that_long(s : seq<T>, r : int) : bool
    {
        exists p : int, q : int | 0 <= p <= q <= |s| && is_true_on_segment(s, p, q) :: q - p == r
    }

    //Functions and Methods

    /** This function is called to initialize the variables that we are going to need at the
    *   main method.
    *   Receives:
    *       - (v) -> array 
    *   Returns: 
    *       - (r) -> The initialized number of segments that fulfills the property 
    *       - [s, n) -> The least indexes of the segment such that satisfies the property
    */
    method variable_initialization(v : array<T>) returns (r : int, s: int, n : int)
    ensures 0 <= s <= n <= v.Length
    ensures r == seg_long_max(v[..], 0, n).0 
    ensures s == seg_long_max(v[..], 0, n).1


    /** 
    *   The function is used as a recursive definition for the calculation of the longest segment,
    *   we will use it to ensure that in each entrance in the loop we do our search correctly. 
    *   We will use to prove different lemmas.
    *   Returns a pair (r, s) where:
    *    
    *   - (r) represents the legth of the longest segments that holds a property. 
    *   - (s) represents the first index such that [s, fin) fulfills the property.
    */
    ghost function seg_long_max(v : seq<T>, ini : int, fin : int) : (int, int)
    decreases fin - ini
    requires 0 <= ini <= fin <= |v|

    /** This method is used to update the lower limit (old_s) of the longest segment that holds the property
    *   and its upper limit is the integer (new_k), when we increase the upper limit by one. 
    *   Receives:
    *   - (v) -> array
    *   - (ini) -> First index of the segment we are studiying
    *   - (old_s) -> The "old" lower index of the longest segment [p, new_k - 1) where ini <= p < new_k - 1
    *   - (new_k) -> The "new" upper index
    */
    method update_actual_s(v : array<T>, ini : int, old_s : int, new_n : int) returns (new_s : int)
    requires 0 <= ini <= old_s < new_n <= v.Length
    requires old_s == seg_long_max(v[..], ini, new_n - 1).1
    ensures 0 <= new_s <= new_n
    ensures new_s == seg_long_max(v[..], ini, new_n).1
    
    /** This method is used to update the maximum of the lengths (r) found until now.
    *   Receives: 
    *   - (v) -> array
    *   - (old_r) -> The "old" max of the lengths
    *   - (old_n) -> The "old" upper limit of the segments we are studiying (*, old_n)
    *   - (new_s) -> The "new_s" we calculated after calling "update_actual_s"
    */
    method update_actual_seg_length(v : array<T>, old_r : int, old_n : int, new_s : int) returns (new_r : int)
    requires 0 <= old_n < v.Length
    requires old_r == seg_long_max(v[..], 0, old_n).0
    requires new_s == seg_long_max(v[..], 0, old_n + 1).1
    ensures new_r == seg_long_max(v[..], 0, old_n + 1).0

    /** This method is the main one, is the one the user will use. Solves the problem we are studiying.
    *   Receives:
    *       - (v) -> array
    *   Returns:
    *       - (r) -> length of the longest segments that holds the property. 
    */
    method mseg_long_max(v : array<T>) returns (r : int)
    ensures there_is_a_segment_that_long(v[..], r)
    ensures is_longest_segment(v[..], r)

    //Lemmas

    /** This lemma ensures that:
        1) There is a segment that holds the property and its length is (r)
        2) There is a segment that holds the property and its lower bound is (s)
    */
    lemma seg_long_max_existence(v : seq<T>, ini : int, fin : int)
    requires 0 <= ini <= fin <= |v|
    ensures exists p, q | ini <= p <= q <= fin && is_true_on_segment(v, p, q) :: q - p == seg_long_max(v, ini, fin).0
    ensures exists p | ini <= p <= fin && is_true_on_segment(v, p, fin) :: p == seg_long_max(v, ini, fin).1

    /** This lemma ensures that the function "seg_long_max" will return an (r, _) such that no
    *   other segment that fulfills the property has a greater length than (r)
    */
    lemma seg_long_max_snd(v : seq<T>, ini : int, fin : int)
    requires 0 <= ini <= fin <= |v|
    ensures forall p, q | ini <= p <= q <= fin && is_true_on_segment(v, p, q) :: q - p <= seg_long_max(v, ini, fin).0


    lemma allways_gt(s : seq<T>, fin : int)
    requires 0 <= fin <= |s|
    ensures seg_long_max(s, 0, fin).0 >= fin - seg_long_max(s, 0, fin).1

    lemma seg_long_max_gt(s : seq<T>, ini : int, fin : int)
    requires 0 <= ini <= fin <= |s| //Estaba estricto antes
    ensures seg_long_max(s, ini, fin).0 >= 0

    lemma upper_limit(s : seq<T>, ini : int, fin : int)
    decreases fin - ini
    requires 0 <= ini < fin <= |s|
    ensures seg_long_max(s, ini, fin).1 <= fin
}

