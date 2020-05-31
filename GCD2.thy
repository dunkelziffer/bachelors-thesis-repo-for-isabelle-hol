(*  Title:      GCD2.thy
    Author:     Klaus Weidinger, TU Muenchen
    Copyright   2020

A simproc for the function "gcd (a::nat) (b::nat)" from "GCD.thy".
*)

theory GCD2
  imports
    Main
    Complex_Main
    "HOL-Computational_Algebra.Primes"
    "HOL-Number_Theory.Prime_Powers"
    HOL.Num
    Coprime
begin

text\<open>
Case distinction:
  case "a = 0 & b = 0": lemma 'gcd_0_0'
  case "a ~= 0 | b ~= 0": lemma 'gcd_eq'
\<close>

lemma gcd_eq:
  fixes a::nat and b::nat and s::nat and t::nat
  assumes "d * s = a" "d * t = b" "d > 0" "coprime s t"
  shows "gcd a b \<equiv> d"
proof -
  have "gcd (d * s) (d * t) = normalize (d * gcd s t)"
    by (auto simp: gcd_mult_left)
  hence "gcd a b = normalize (d * gcd s t)"
    using assms by simp
  hence "gcd a b = normalize d"
    using assms and coprime_iff_gcd_eq_1 by simp
  hence "gcd a b = d" using assms by simp
  thus "gcd a b \<equiv> d" by (simp add: eq_reflection)
qed

lemma gcd_0_0: "gcd (0::nat) (0::nat) \<equiv> 0"
  by simp

ML_file\<open>algorithms.ML\<close>
ML_file\<open>tools.ML\<close>

ML\<open>
signature GCD2 =
sig

val parse: Thm.cterm -> int * int

(*                            a     b     gcd    s     t      *)
datatype cert = GCD_CERT of (int * int) * int * int * int | ZERO_ZERO
val mk_cert: int -> int -> cert
val generate_proof: Proof.context -> cert -> thm option

val prove: Proof.context -> int * int -> thm option
val simproc: Proof.context -> Thm.cterm -> thm option

(* helper tools *)
val get_cert_numbers : cert -> (int * int)

end


structure Gcd2 : GCD2 =
struct

(*                            a     b     gcd    s     t      *)
datatype cert = GCD_CERT of (int * int) * int * int * int | ZERO_ZERO

fun parse ct = Tools.parse2 ct @{const_name "gcd"}

fun mk_cert a b =
    if (a = 0) andalso (b = 0) then ZERO_ZERO else
    let val gcd = Algorithms.euclid a b
    in
        GCD_CERT ((a, b), gcd, a div gcd, b div gcd)
    end

exception ERROR
fun generate_proof _ ZERO_ZERO =
        @{thm gcd_0_0}
            |> SOME
  | generate_proof ctxt (GCD_CERT ((a, b), gcd, s, t)) = 
    let
      val coprime_s_t = case Coprime.prove_true ctxt (s, t) of SOME thm => thm |
                                                                   NONE => raise ERROR
    in
        @{thm gcd_eq}
            |> Drule.infer_instantiate' ctxt 
                  (map (Tools.nat2ct' ctxt) [gcd, s, a, t, b])
            |> Tools.simp ctxt 3
            |> (fn thm => thm OF [coprime_s_t])
            |> SOME
    end

fun prove ctxt (a, b) =               (* (a, b)          *)
    (a,b) |-> mk_cert                 (* cert            *)
          |> generate_proof ctxt      (* thm option      *)
    handle ERROR => NONE

fun simproc ctxt input =            (* term            *)
    input |> parse                  (* n               *)
          |> prove ctxt             (* thm option      *)
    handle TERM _ => NONE

(* helper tools *)
fun get_cert_numbers ZERO_ZERO = (0, 0)
  | get_cert_numbers (GCD_CERT (ab, _, _, _)) = ab

end
\<close>

simproc_setup gcd_simproc ("gcd (numeral a::nat) (numeral b::nat)") = \<open>K Gcd2.simproc\<close>

end