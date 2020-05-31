(*  Title:      Coprime.thy
    Author:     Klaus Weidinger, TU Muenchen
    Copyright   2020

A simproc for the predicate "coprime (a::nat) (b::nat)" from "Rings.thy".
*)

theory Coprime
  imports
    Main
    Complex_Main
    "HOL-Computational_Algebra.Primes"
    "HOL-Number_Theory.Prime_Powers"
    HOL.Num
begin

text\<open>
Case distinction:
  case "a = 0 & b = 0": lemma 'coprime_0_0'
  case "(a ~=0 | b ~= 0) & coprime a b": lemma 'coprime_true'
  case "(a ~=0 | b ~= 0) & ~coprime a b": lemma 'coprime_false'
\<close>

lemma coprimeI_bezout:
  assumes "a * s + b * t = 1" 
  shows   "coprime a b"
proof (rule coprimeI)
  fix d assume "d dvd a" "d dvd b"
  hence "d dvd (a * s + b * t)"
    by auto
  also have "\<dots> = 1"
    by fact
  finally show "d dvd 1" .
qed

lemma coprime_true:
  fixes a::nat and b::nat and s::int and t::int
  assumes "int a * s + int b * t = 1" 
  shows "coprime a b"
proof -
  from assms have "coprime (int a) (int b)"
    by (intro coprimeI_bezout) auto
  thus "coprime a b" by simp
qed

lemma coprime_false:
  fixes a::nat and b::nat
  assumes "d * ka = a" "d * kb = b" "d \<noteq> 1"
  shows "\<not> coprime a b"
proof -
  show "\<not> coprime a b" using assms by (auto simp: not_coprimeI)
qed

lemma coprime_0_0: "\<not> coprime (0::nat) (0::nat)"
  by simp


ML_file\<open>algorithms.ML\<close>
ML_file\<open>tools.ML\<close>

ML\<open>
signature COPRIME =
sig

val parse: Thm.cterm -> int * int

(*                               a     b      s     t                  a     b      d       *)
datatype cert = BEZOUT_CERT of (int * int) * int * int | GCD_GT_1 of (int * int) * int | ZERO_ZERO
val mk_cert: int -> int -> cert
val generate_proof: Proof.context -> cert -> thm option

val prove: Proof.context -> int * int -> thm option
val simproc: Proof.context -> Thm.cterm -> thm option

(* helper tools *)
val get_cert_numbers : cert -> (int * int)
val prove_true: Proof.context -> int * int -> thm option

end


structure Coprime : COPRIME =
struct

(*                               a     b      s     t                  a     b      d       *)
datatype cert = BEZOUT_CERT of (int * int) * int * int | GCD_GT_1 of (int * int) * int | ZERO_ZERO

fun parse ct = Tools.parse2 ct @{const_name "coprime"}

fun mk_cert 0 0 = ZERO_ZERO
  | mk_cert a b =
        let val (gcd, s, t) = Algorithms.ext_euclid a b
        in
            if gcd = 1 then BEZOUT_CERT ((a, b), s, t) else GCD_GT_1 ((a, b), gcd)
        end

fun generate_proof _ ZERO_ZERO =
        @{thm coprime_0_0}
            |> SOME
  | generate_proof ctxt (BEZOUT_CERT ((a, b), s, t)) =
        let val N = HOLogic.natT
            val Z = HOLogic.intT
        in
        @{thm coprime_true}
            |> Drule.infer_instantiate' ctxt
                  (map (Tools.num2ct' ctxt) [(N, a), (Z, s), (N, b), (Z, t)])
            |> Tools.simp ctxt 1
            |> SOME
        end
  | generate_proof ctxt (GCD_GT_1 ((a, b), d)) =
        @{thm coprime_false}
            |> Drule.infer_instantiate' ctxt
                  (map (Tools.nat2ct' ctxt) [d, a div d, a, b div d, b])
            |> Tools.simp ctxt 3
            |> SOME

fun prove ctxt (a, b) =             (* (a, b)        *)
    (a,b) |-> mk_cert               (* cert          *)
          |> generate_proof ctxt    (* thm option    *)

fun simproc ctxt input =            (* term            *)
    input |> parse                  (* n               *)
          |> prove ctxt             (* thm option      *)
          |> Tools.wrap             (* thm option      *)
    handle TERM _ => NONE

(* helper tools *)
fun get_cert_numbers ZERO_ZERO = (0, 0)
  | get_cert_numbers (BEZOUT_CERT (ab, _, _)) = ab
  | get_cert_numbers (GCD_GT_1 (ab, _)) = ab

fun prove_true ctxt (a, b) =
    let val thm' = prove ctxt (a, b)
        fun discard_not_coprime NONE = NONE
          | discard_not_coprime (SOME thm) =
                case Thm.prop_of thm 
                  of (Const("HOL.Trueprop", _) $ (Const("HOL.Not", _) $ _)) => NONE |
                                                                          _ => SOME thm
    in
        discard_not_coprime thm'
    end

end
\<close>

simproc_setup coprime_simproc ("coprime (numeral a::nat) (numeral b::nat)") = \<open>K Coprime.simproc\<close>

end