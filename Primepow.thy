(*  Title:      Primepow.thy
    Author:     Klaus Weidinger, TU Muenchen
    Copyright   2020

A simproc for the predicate "primepow (n::int)" from "Prime_Powers.thy".
*)

theory Primepow
  imports
    Main
    Complex_Main
    "HOL-Computational_Algebra.Primes"
    "HOL-Number_Theory.Prime_Powers"
    HOL.Num
    Prime
begin

text\<open>
Case distinction:
  case "n < 2": lemma 'primepow_false_lt2'
  case "n >= 2 & primepow n": lemma 'primepow_true'
  case "n >= 2 & ~primepow n": lemma 'primepow_false'
\<close>

lemma primepow_true:
  fixes p::nat and pp::nat
  assumes "p ^ m = pp" "m > 0" "prime p"
  shows "primepow pp"
proof -
  show "primepow pp" using assms by (auto simp: primepow_def)
qed

lemma primepow_false:
  fixes a::nat and b::nat and pp::nat
  assumes "a * ka = pp" "b * kb = pp" "a \<noteq> b" "prime a" "prime b"
  shows "\<not> primepow pp"
proof -
  have tmp: "a dvd pp" using assms and dvd_def by metis
  have "b dvd pp" using assms and dvd_def by metis
  thus "\<not> primepow pp" using assms and tmp by (auto simp: not_primepowI)
qed

lemma primepow_false_lt2:
  fixes n::nat
  assumes "n = 0 \<or> n = 1"
  shows "\<not> primepow n"
  using assms by auto

ML_file\<open>algorithms.ML\<close>
ML_file\<open>tools.ML\<close>

ML\<open>
signature PRIMEPOW =
sig

(* defines the upper (and lower) bound for the simproc *)
val limit: int Config.T

val parse: Thm.cterm -> int

(*                            pp    p     m                   pp    a     b   *)
datatype cert = TRUE_CERT of int * int * int | FALSE_CERT of int * int * int | LESS_THAN_2 of int
val mk_cert: int -> cert
val generate_proof: Proof.context -> cert -> thm option

val prove: Proof.context -> int -> thm option
val simproc: Proof.context -> Thm.cterm -> thm option

(* helper tools *)
val get_cert_number : cert -> int

end


structure Primepow : PRIMEPOW =
struct

val limit = Attrib.setup_config_int \<^binding>\<open>limit\<close> (K 1000000);
exception LIMIT

(*                            pp    p     m                   pp    a     b   *)
datatype cert = TRUE_CERT of int * int * int | FALSE_CERT of int * int * int | LESS_THAN_2 of int

fun parse ct = Tools.parse1 ct @{const_name "primepow"}

fun mk_cert n =
    if n < 2 then LESS_THAN_2 n else
    let
        val fs_mset = Algorithms.to_mset (Algorithms.factorize n)
    in
        if length fs_mset = 1 then TRUE_CERT (n, fst (hd fs_mset), snd (hd fs_mset))
                              else FALSE_CERT (n, fst (hd fs_mset), fst (hd (tl fs_mset)))
    end

exception ERROR
fun generate_proof ctxt (LESS_THAN_2 pp) =
        @{thm primepow_false_lt2}
            |> Drule.infer_instantiate' ctxt [Tools.nat2ct' ctxt pp]
            |> Tools.simp ctxt 1
            |> SOME
  | generate_proof ctxt (TRUE_CERT (pp, p, m)) =
    let 
        val prime_p = case fst (Pratt.prove_prime [] p ctxt) 
                        of SOME thm => thm |
                               NONE => raise ERROR
    in
        @{thm primepow_true}
            |> Drule.infer_instantiate' ctxt
                      (map (Tools.nat2ct' ctxt) [p, m, pp])
            |> Tools.simp ctxt 2
            |> (fn thm => thm OF [prime_p])
            |> SOME
    end
  | generate_proof ctxt (FALSE_CERT (pp, a, b)) =
    let 
        val prime_a = case fst (Pratt.prove_prime [] a ctxt) 
                        of SOME thm => thm |
                               NONE => raise ERROR
        val prime_b = case fst (Pratt.prove_prime [] b ctxt) 
                        of SOME thm => thm |
                               NONE => raise ERROR
    in
        @{thm primepow_false}
            |> Drule.infer_instantiate' ctxt
                      (map (Tools.nat2ct' ctxt) [a, pp div a, pp, b, pp div b])
            |> Tools.simp ctxt 3
            |> (fn thm => thm OF [prime_a])
            |> (fn thm => thm OF [prime_b])
            |> SOME
    end

fun prove ctxt n =                   (* term                            *)
    n     |> mk_cert                 (* cert                            *)
          |> generate_proof ctxt     (* thm option                      *)
    handle ERROR => NONE
         | THM _ => NONE

fun simproc ctxt input =            (* term            *)
    input |> parse                  (* n               *)
          |> (fn n => if abs n < Config.get ctxt limit then n else raise LIMIT)
          |> prove ctxt             (* thm option      *)
          |> Tools.wrap             (* thm option      *)
    handle LIMIT => NONE
         | TERM _ => NONE

(* helper tools *)
fun get_cert_number (LESS_THAN_2 pp) = pp
  | get_cert_number (TRUE_CERT (pp, _, _)) = pp
  | get_cert_number (FALSE_CERT (pp, _, _)) = pp

end
\<close>

simproc_setup primepow_simproc ("primepow (numeral n::nat)") = \<open>K Primepow.simproc\<close>

end