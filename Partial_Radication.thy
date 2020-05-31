(*  Title:      Partial_Radication.thy
    Author:     Klaus Weidinger, TU Muenchen
    Copyright   2020

A simproc for the function "root (n::nat) (x::nat)" from "NthRoot.thy".
*)

theory Partial_Radication
  imports
    Complex_Main
    "HOL-Computational_Algebra.Primes"
    "HOL-Computational_Algebra.Nth_Powers"
    HOL.Num
    "HOL.Real"
begin

text\<open>
Case distinction:
  case "n = 0": lemma 'root_0' from 'NthRoot.thy'
  case "n = 1": lemma 'root_1'
  case "n > 1": lemma 'partial_radication'
\<close>

lemma partial_radication:
  fixes n::nat and x::nat and c::nat and x'::nat
  assumes "x = x' * c ^ n" "c > 0" "n > 1"
  shows "root n (real x) \<equiv> c * root n (real x')"
proof -
  have "0 \<le> c"
    using assms(2) by auto
  hence "root n (real x) = root n (real x') * root n (real (c ^ n))"
    using assms by (auto simp: real_root_mult)
  hence "root n (real x) = root n (real x') * c" 
    using assms by (auto simp: real_root_power_cancel)
  hence "root n (real x) = c * root n (real x')"
    by simp
  thus "root n (real x) \<equiv> c * root n (real x')" by (simp add: eq_reflection)
qed

lemma root_0': "root 0 (real (x::nat)) \<equiv> 0"
  by simp

lemma root_1: "root 1 (real (x::nat)) \<equiv> x"
  by simp


ML_file\<open>algorithms.ML\<close>
ML_file\<open>tools.ML\<close>

ML\<open>
signature PARTIAL_RADICATION =
sig

(* defines the upper (and lower) bound for the simproc *)
val limit: int Config.T

val parse: Thm.cterm -> int * int

(*                                n     x      c     x'   *)
datatype cert = P_RADIX_CERT of (int * int) * int * int | ZEROTH_ROOT of int | FIRST_ROOT of int
val mk_cert: int -> int -> cert
val generate_proof: Proof.context -> cert -> thm option

val prove: Proof.context -> int * int -> thm option
val simproc: Proof.context -> Thm.cterm -> thm option

(* helper tools *)
val get_cert_numbers : cert -> int * int

end


structure Partial_Radication : PARTIAL_RADICATION =
struct

val limit = Attrib.setup_config_int \<^binding>\<open>limit\<close> (K 1000000);
exception LIMIT

(*                                n     x      c     x'   *)
datatype cert = P_RADIX_CERT of (int * int) * int * int | ZEROTH_ROOT of int | FIRST_ROOT of int

fun parse ct = Tools.parseZR ct @{const_name "root"}

fun mk_cert n x =
    if n = 0 then ZEROTH_ROOT x else
    if n = 1 then FIRST_ROOT x else
    let
        val fs_mset = Algorithms.to_mset (Algorithms.factorize x)
        fun p_radix acc_c acc_x' (n, x) ((p, m)::pms) = p_radix ((p, m div n)::acc_c) ((p, m mod n)::acc_x') (n, x) pms
          | p_radix acc_c acc_x' (n, x) [] = P_RADIX_CERT ((n, x), Algorithms.prod_mset acc_c, Algorithms.prod_mset acc_x')
    in
        p_radix [] [] (n, x) fs_mset
    end

exception ERROR
fun generate_proof ctxt (ZEROTH_ROOT x) =
        @{thm root_0'}
            |> Drule.infer_instantiate' ctxt [Tools.nat2ct' ctxt x]
            |> SOME
  | generate_proof ctxt (FIRST_ROOT x) =
        @{thm root_1}
            |> Drule.infer_instantiate' ctxt [Tools.nat2ct' ctxt x]
            |> SOME
  | generate_proof ctxt (P_RADIX_CERT ((n, x), c, x')) =
        if c = 1 then raise ERROR else
        @{thm partial_radication}
            |> Drule.infer_instantiate' ctxt
                      (map (Tools.nat2ct' ctxt) [x, x', c, n])
            |> Tools.simp ctxt 2
            |> SOME

fun prove ctxt (n, x) =               (* (n, x)         *)
    (n,x) |-> mk_cert                 (* cert           *)
          |> generate_proof ctxt      (* thm option     *)
    handle ERROR => NONE

fun simproc ctxt input =            (* term            *)
    input |> parse                  (* n, x            *)
          |> (fn (n, x) => if abs x < Config.get ctxt limit then (n, x) else raise LIMIT)
          |> prove ctxt             (* thm option      *)
    handle LIMIT => NONE
         | TERM _ => NONE

(* helper tools *)
fun get_cert_numbers (ZEROTH_ROOT x) = (0, x)
  | get_cert_numbers (FIRST_ROOT x) = (1, x)
  | get_cert_numbers (P_RADIX_CERT ((n, x), _, _)) = (n, x)

end
\<close>

simproc_setup root_simproc ("root (numeral n::nat) (real (numeral x::nat))") = \<open>K Partial_Radication.simproc\<close>

end