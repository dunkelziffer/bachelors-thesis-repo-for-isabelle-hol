(*  Title:      Prime.thy
    Author:     Klaus Weidinger, TU Muenchen
    Copyright   2020

A simproc for the predicate "prime (n::int)" from "Factorial_Ring.thy".
*)

theory Prime
  imports
    Main
    Complex_Main
    "HOL-Computational_Algebra.Primes"
    HOL.Num
    "Pratt_Certificate.Pratt_Certificate"
begin

text\<open>
Case distinction:
  case "n < 2": lemma 'prime_false_lt2'
  case "n >= 2 & prime n": solved with 'Pratt_Certificate.thy'
                           and 'pratt.ML' from the AFP
  case "n >= 2 & ~prime n": lemma 'prime_false'
\<close>

lemma prime_false:
  fixes p::nat
  assumes "p * k = a * b" "\<not> p dvd a" "\<not> p dvd b"
  shows "\<not> prime p"
proof -
  have "p dvd a * b" using assms and dvd_def by metis
  hence "\<not> prime_elem p \<or> \<not> normalize p = p" using assms and prime_elem_def by blast
  thus "\<not> prime p" using prime_def by blast
qed

lemma prime_false_lt2:
  fixes p::nat
  assumes "p = 0 \<or> p = 1"
  shows "\<not> prime p"
  using assms by auto

ML_file\<open>algorithms.ML\<close>
ML_file\<open>tools.ML\<close>

ML\<open>
signature PRIME =
sig

(* defines the upper (and lower) bound for the simproc *)
val limit: int Config.T

val parse: Thm.cterm -> int

(*                        p                     p  =  a  *  b                    p    *)
datatype cert = PRIME of int | DIVISOR_PAIR of int * int * int | LESS_THAN_2 of int
val mk_cert: int -> cert
val generate_proof: Proof.context -> cert -> thm option

val prove: Proof.context -> int -> thm option
val simproc: Proof.context -> Thm.cterm -> thm option

(* helper tools *)
val get_cert_number : cert -> int

end


structure Prime : PRIME =
struct

val limit = Attrib.setup_config_int \<^binding>\<open>limit\<close> (K 1000000);
exception LIMIT

(*                        p                     p  =  a  *  b                    p    *)
datatype cert = PRIME of int | DIVISOR_PAIR of int * int * int | LESS_THAN_2 of int

fun parse ct = Tools.parse1 ct @{const_name "prime"}

fun mk_cert n =
    if n < 2 then LESS_THAN_2 n else
    let
        val sf = Algorithms.smallest_factor n
    in
        if sf = n then PRIME n
                  else DIVISOR_PAIR (n, sf, n div sf)
    end

fun generate_proof ctxt (PRIME n) =
        fst (Pratt.prove_prime [] n ctxt)
  | generate_proof ctxt (DIVISOR_PAIR (p, d1, d2)) =
        @{thm prime_false}
            |> Drule.infer_instantiate' ctxt
                      (map (Tools.nat2ct' ctxt) [p, d1*d2 div p, d1, d2])
            |> Tools.simp ctxt 3
            |> SOME
  | generate_proof ctxt (LESS_THAN_2 n) =
        @{thm prime_false_lt2}
            |> Drule.infer_instantiate' ctxt
                      (map (Tools.nat2ct' ctxt) [n])
            |> Tools.simp ctxt 1
            |> SOME

fun prove ctxt n =
    n     |> mk_cert                (* cert            *)
          |> generate_proof ctxt    (* thm option      *)

fun simproc ctxt input =            (* term            *)
    input |> parse                  (* n               *)
          |> (fn n => if abs n < Config.get ctxt limit then n else raise LIMIT)
          |> prove ctxt             (* thm option      *)
          |> Tools.wrap             (* thm option      *)
    handle LIMIT => NONE
         | TERM _ => NONE

(* helper tools *)
fun get_cert_number (PRIME p) = p
  | get_cert_number (DIVISOR_PAIR (p, _, _)) = p
  | get_cert_number (LESS_THAN_2 p) = p

end
\<close>

simproc_setup prime_simproc ("prime (numeral n::nat)") = \<open>K Prime.simproc\<close>

end