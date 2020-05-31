(*  Title:      Prime.thy
    Author:     Klaus Weidinger, TU Muenchen
    Copyright   2020

A simproc for the predicate "prime_factorization (n::nat)" from "Factorial_Ring.thy".
*)

theory Prime_Factorization
  imports
    Main
    Complex_Main
    "HOL-Computational_Algebra.Primes"
    HOL.Num
    Prime
begin

text\<open>Lemmata for prime_factorization (n::nat):\<close>

text\<open>Ball = bounded universal quantor\<close>
text\<open>"Multiset.Ball P prime" = all elements of P are prime\<close>

lemma prime_factorization_eqI_nat:
  assumes "Multiset.Ball MSet prime" "prod_mset MSet = n"
  shows   "prime_factorization n \<equiv> MSet"
proof -
  have "prime_factorization n = MSet" 
    using assms by (simp add: prime_factorization_eqI)
  thus "prime_factorization n \<equiv> MSet" by (simp add: eq_reflection)
qed

lemma Ball_set_mset_empty: "Multiset.Ball {#} Pred"
  and Ball_set_mset_add:   "Pred n \<Longrightarrow> Multiset.Ball MSet Pred \<Longrightarrow> Multiset.Ball (add_mset n MSet) Pred"
  by auto

lemma prime_factorization_0': "prime_factorization (0::nat) \<equiv> {#}"
  by (auto simp: eq_reflection)

ML_file\<open>algorithms.ML\<close>
ML_file\<open>tools.ML\<close>

ML\<open>
signature PRIME_FACTORIZATION =
sig

(* defines the upper (and lower) bound for the simproc *)
val limit: int Config.T

val parse: Thm.cterm -> int

datatype cert = FACTORIZATION of int * int list | ZERO
val mk_cert: int -> cert
val generate_proof: Proof.context -> cert -> thm option

val prove: Proof.context -> int -> thm option
val simproc: Proof.context -> Thm.cterm -> thm option

(* helper tools *)
val get_cert_number : cert -> int

end


structure Prime_Factorization : PRIME_FACTORIZATION =
struct

val limit = Attrib.setup_config_int \<^binding>\<open>limit\<close> (K 1000000);
exception LIMIT

datatype cert = FACTORIZATION of int * int list | ZERO

fun parse ct = Tools.parse1 ct @{const_name "prime_factorization"}

fun mk_cert n =
    if n = 0 then ZERO
             else FACTORIZATION (n, Algorithms.factorize n)

exception ERROR
fun generate_proof _ ZERO =
    SOME @{thm prime_factorization_0'}
  | generate_proof ctxt (FACTORIZATION (n, fs)) =
    let
      (* initialize theorem "forall x in mset. prime x" *)
      val all_fs_prime_0 = @{thm Ball_set_mset_empty[of "prime :: nat \<Rightarrow> bool"]}
      (* iteratively fill elements into theorem *)
      fun build_thm [] all_fs_prime_iter = all_fs_prime_iter
        | build_thm (f::fs) all_fs_prime_iter =
                let val prime_f = case fst (Pratt.prove_prime [] f ctxt) 
                                    of SOME thm => thm |
                                           NONE => raise ERROR
                in
                    build_thm fs (@{thm Ball_set_mset_add} OF [prime_f, all_fs_prime_iter])
                end
      val all_fs_prime = build_thm fs all_fs_prime_0
    in
        @{thm prime_factorization_eqI_nat}
            |> (fn thm => thm OF [all_fs_prime])
            |> Drule.infer_instantiate' ctxt (map (Tools.nat2ct' ctxt) [n])
            |> Tools.simp ctxt 1
            |> SOME
    end

fun prove ctxt n =                  (* n               *)
    n     |> mk_cert                (* cert            *)
          |> generate_proof ctxt    (* thm option      *)
    handle ERROR => NONE

fun simproc ctxt input =            (* term            *)
    input |> parse                  (* n               *)
          |> (fn n => if abs n < Config.get ctxt limit then n else raise LIMIT)
          |> prove ctxt             (* thm option      *)
    handle LIMIT => NONE
         | TERM _ => NONE

(* helper tools *)
fun get_cert_number ZERO = 0
  | get_cert_number (FACTORIZATION (n, _)) = n

end
\<close>

simproc_setup prime_factorization_simproc ("prime_factorization (numeral n::nat)") = \<open>K Prime_Factorization.simproc\<close>

end