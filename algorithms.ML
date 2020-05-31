signature ALGORITHMS = 
sig

(* MATH *)
val factorize: int -> int list  (* returns factors in descending order *)
val smallest_factor: int -> int
val euclid: int -> int -> int
val ext_euclid: int -> int -> int * int * int  (* returns gcd and Bezout-witnesses s and t *)

(* DATASTRUCTURES *)
val to_mset: int list -> (int * int) list  (* reverses order *)
val prod_mset: (int * int) list -> int

end

structure Algorithms : ALGORITHMS = 
struct

(* MATH *)

(* n, factor list, current test, bool (test = 6n+1)   *)
fun factorize' 1 fs _ _ = fs
  | factorize' n fs 2 _ = if n mod 2 = 0 then factorize' (n div 2) (2::fs) 2 false
                                         else factorize' n fs 3 false
  | factorize' n fs 3 _ = if n mod 3 = 0 then factorize' (n div 3) (3::fs) 3 false
                                         else factorize' n fs 5 false
  | factorize' n fs t false = if t*t > n then n::fs
                     else if n mod t = 0 then factorize' (n div t) (t::fs) t false
                                         else factorize' n fs (t+2) true
  | factorize' n fs t true =  if t*t > n then n::fs 
                     else if n mod t = 0 then factorize' (n div t) (t::fs) t true
                                         else factorize' n fs (t+4) false

fun factorize n = factorize' n [] 2 false


(* n, current test, bool (test = 6n+1)   *)
fun smallest_factor' 1 _ _ = 1
  | smallest_factor' n 2 _ = if n mod 2 = 0 then 2
                                            else smallest_factor' n 3 false
  | smallest_factor' n 3 _ = if n mod 3 = 0 then 3
                                            else smallest_factor' n 5 false
  | smallest_factor' n t false = if t*t > n then n
                        else if n mod t = 0 then t
                                            else smallest_factor' n (t+2) true
  | smallest_factor' n t true  = if t*t > n then n
                        else if n mod t = 0 then t
                                            else smallest_factor' n (t+4) false

fun smallest_factor n = smallest_factor' n 2 false


fun euclid a b = if b = 0 then a
                          else euclid b (a mod b)


fun ext_euclid a b = if b = 0 then (a, 1, 0)
                                 else let val (d, s, t) = ext_euclid b (a mod b)
                                 in (d, t, s-(t*(a div b)))
                                 end


(* DATASTRUCTURES *)

fun to_mset' [] _ _ = []
  | to_mset' (f1::f2::fs) mset m = if f1 = f2 then to_mset' (f2::fs) mset (m+1)
                                              else to_mset' (f2::fs) ((f1, m+1)::mset) 0
  | to_mset' (f1::[]) mset m = (f1, m+1)::mset

fun to_mset set = to_mset' set [] 0


fun prod_mset [] = 1
  | prod_mset ((p : int, m)::pms) = IntInf.pow (p, m) * prod_mset pms

end