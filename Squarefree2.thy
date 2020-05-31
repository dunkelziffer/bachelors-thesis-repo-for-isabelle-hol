(*  Title:      Squarefree2.thy
    Author:     Klaus Weidinger, TU Muenchen
    Copyright   2020

A simproc for the predicate "prime (n::int)" from "Squarefree.thy".
*)

theory Squarefree2
  imports
    Main
    Complex_Main
    "HOL-Computational_Algebra.Primes"
    "HOL-Computational_Algebra.Nth_Powers"
    "HOL-Computational_Algebra.Squarefree"
    "HOL-Number_Theory.Prime_Powers"
    HOL.Num
    Prime
begin

text\<open>
Case distinction:
  case "n = 0": lemma 'not_squarefree_0' from 'Squarefree.thy'
  case "n > 0 & squarefree n": lemma 'squarefree_true'
  case "n > 0 & ~squarefree n": lemma 'squarefree_false'
\<close>

lemma squarefree_true:
  fixes n :: "'a :: factorial_semiring_gcd"
  assumes "list_all prime xs" "prod_list xs = n" "distinct xs"
  shows "squarefree n"
proof -
  have "squarefree (\<Prod>(set xs))"
    using assms
    by (intro squarefree_prod_coprime) (auto simp: list_all_iff squarefree_prime primes_coprime)
  also have "(\<Prod>(set xs)) = n"
    using assms by (subst prod.distinct_set_conv_list) auto
  finally show "squarefree n" by simp
qed

lemma list_all_Nil: "list_all P []"
  by simp

lemma list_all_ConsI: "P x \<Longrightarrow> list_all P xs \<Longrightarrow> list_all P (x # xs)"
  by auto

lemma squarefree_false:
  fixes sf::nat
  assumes "x^2 * k = sf" "x > 1"
  shows "\<not> squarefree sf"
proof -
  have "x^2 dvd sf \<and> x > 1" using assms by (auto simp: dvd_def)
  thus "\<not> squarefree sf" by (auto simp: not_squarefreeI)
qed


ML_file\<open>algorithms.ML\<close>
ML_file\<open>tools.ML\<close>

ML\<open>
signature SQUAREFREE =
sig

(* defines the upper (and lower) bound for the simproc *)
val limit: int Config.T

val parse: Thm.cterm -> int

(*                            n     factors                  n   square    *)
datatype cert = TRUE_CERT of int * int list | FALSE_CERT of int * int | ZERO
val mk_cert: int -> cert
val generate_proof: Proof.context -> cert -> thm option

val prove: Proof.context -> int -> thm option
val simproc: Proof.context -> Thm.cterm -> thm option

(* helper tools *)
val get_cert_number : cert -> int

end


structure Squarefree : SQUAREFREE =
struct

val limit = Attrib.setup_config_int \<^binding>\<open>limit\<close> (K 1000000);
exception LIMIT

(*                            n     factors                  n   duplicate    *)
datatype cert = TRUE_CERT of int * int list | FALSE_CERT of int * int | ZERO

fun parse ct = Tools.parse1 ct @{const_name "squarefree"}

(* "no_duplicates" assumes that factor list is ordered (here in descending order)   *)
fun mk_cert n =
    if n = 0 then ZERO else
    let 
        val factors = Algorithms.factorize n
        fun no_duplicates (f1::f2::fs) = if f1 = f2 then (false, f1)
                                                    else no_duplicates (f2::fs)
          | no_duplicates _ = (true, 1)
        val result = no_duplicates factors
    in
        if fst result then TRUE_CERT (n, factors)
                      else FALSE_CERT (n, snd result)
    end

exception ERROR
fun generate_proof _ ZERO =
          SOME @{thm not_squarefree_0}
  | generate_proof ctxt (TRUE_CERT (n, fs)) = 
    let
      (* initialize theorem "forall x in list. prime x" *) 
      val all_fs_prime_0 = @{thm list_all_Nil[of "prime :: nat \<Rightarrow> bool"]}
      (* iteratively fill elements into theorem *)
      fun build_thm [] all_fs_prime_iter = all_fs_prime_iter
        | build_thm (f::fs) all_fs_prime_iter = 
            let val prime_f = case fst (Pratt.prove_prime [] f ctxt) 
                                of SOME thm => thm |
                                       NONE => raise ERROR
            in
                build_thm fs (@{thm list_all_ConsI} OF [prime_f, all_fs_prime_iter])
            end
      val all_fs_prime = build_thm fs all_fs_prime_0
    in
        @{thm squarefree_true}
            |> (fn thm => thm OF [all_fs_prime])
            |> Drule.infer_instantiate' ctxt
                  (map (Tools.nat2ct' ctxt) [n])
            |> Tools.simp ctxt 2
            |> SOME
    end
  | generate_proof ctxt (FALSE_CERT (n, x)) =
        @{thm squarefree_false}
            |> Drule.infer_instantiate' ctxt
                  (map (Tools.nat2ct' ctxt) [x, n div (x*x), n])
            |> Tools.simp ctxt 2
            |> SOME

fun prove ctxt n =                  (* n                            *)
    n     |> mk_cert                (* cert                         *)
          |> generate_proof ctxt    (* thm option                   *)
    handle ERROR => NONE

fun simproc ctxt input =            (* term            *)
    input |> parse                  (* n               *)
          |> (fn n => if abs n < Config.get ctxt limit then n else raise LIMIT)
          |> prove ctxt             (* thm option      *)
          |> Tools.wrap             (* thm option      *)
    handle LIMIT => NONE
         | TERM _ => NONE

(* helper tools *)
fun get_cert_number ZERO = 0
  | get_cert_number (TRUE_CERT (n, _)) = n
  | get_cert_number (FALSE_CERT (n, _)) = n

end
\<close>

simproc_setup squarefree_simproc ("squarefree (numeral n::nat)") = \<open>K Squarefree.simproc\<close>

end