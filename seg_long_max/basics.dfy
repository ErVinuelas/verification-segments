/** This file contains modules that are used in different
*   modules that model more complex problems and algortihms
*/

module BasicFunctions {
    /** Receives to integers and returns the greatest */
    ghost function max(a: int, b: int): int
    ensures (max(a, b) == b && b > a) || (max(a,b) == a && a >= b)
    {
        if a < b then b else a
    }
}

module BasicMethods {
    import BasicFunctions
    
    /** Receives to integers and returns the greatest, like BasicFunctions.max */
    method mmax(a : int, b: int) returns (m : int)
    ensures m == BasicFunctions.max(a, b)
    {
        if a < b { return b; } else { return a; }
    }
}