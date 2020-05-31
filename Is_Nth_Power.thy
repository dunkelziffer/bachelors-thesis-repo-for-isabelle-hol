(*  Title:      Is_Nth_Power.thy
    Author:     Klaus Weidinger, TU Muenchen
    Copyright   2020

A simproc for the predicate "is_nth_power (n::nat) (x::nat)" from "Nth_Powers.thy".
*)

theory Is_Nth_Power
  imports
    Main
    Complex_Main
    "HOL-Computational_Algebra.Primes"
    "HOL-Computational_Algebra.Nth_Powers"
    HOL.Num
    Prime
begin

text\<open>
Case distinction:
  case "n = 0 & x = 1": lemma 'is_zeroth_power_of_1'
  case "n = 0 & x ~= 1": lemma 'is_zeroth_power_false'
  case "n ~= 0 & x = 0": lemma 'is_nth_power_0' from 'Nth_Power.thy'
  case "n ~= 0 & x ~= 0 & is_nth_power n x": lemma 'is_nth_power_true'
  case "n ~= 0 & x ~= 0 & ~is_nth_power n x": lemma 'is_nth_power_false'
\<close>

lemma is_nth_power_true:
  fixes n::nat and x::nat
  assumes "b ^ n = x"
  shows "is_nth_power n x"
proof -
  show "is_nth_power n x" using assms by (auto simp: is_nth_power_def)
qed

lemma is_nth_power_false:
  fixes n::nat and x::nat
  assumes "prime p" "p^m * k = x" "\<not> p^(m+1) dvd x" "\<not> n dvd m" "n > 0"
  shows "\<not> is_nth_power n x"
proof -
  have tmp: "multiplicity p x = m" using assms by (auto simp: multiplicity_eqI)
  have "n > 0 \<longrightarrow> \<not>(\<forall>p. prime p \<longrightarrow> n dvd multiplicity p x) \<longrightarrow> \<not> is_nth_power n x"
    using is_nth_power_conv_multiplicity_nat by simp
  hence "\<not>(\<forall>p. prime p \<longrightarrow> n dvd multiplicity p x) \<longrightarrow> \<not> is_nth_power n x"
    using assms by auto
  hence "(\<exists>p. \<not>(prime p \<longrightarrow> n dvd multiplicity p x)) \<longrightarrow> \<not> is_nth_power n x"
    using not_all by simp
  hence "(\<exists>p. (prime p & \<not> n dvd multiplicity p x)) \<longrightarrow> \<not> is_nth_power n x"
    using not_imp by simp
  thus "\<not> is_nth_power n x" using assms and tmp by auto
qed

lemma is_zeroth_power_of_1: "is_nth_power 0 1"
  by simp

lemma is_zeroth_power_false:
  fixes x::nat
  assumes "x \<noteq> 1"
  shows "\<not> is_nth_power 0 x"
proof -
  show "\<not> is_nth_power 0 x" using assms by simp
qed


ML_file\<open>algorithms.ML\<close>
ML_file\<open>tools.ML\<close>

ML\<open>
signature IS_NTH_POWER =
sig

(* defines the upper (and lower) bound for the simproc *)
(* only on second argument, as that needs to be factorized *)
val limit: int Config.T

val parse: Thm.cterm -> int * int

(*                             n     x     base                  n     x    prime  mult.   *)
datatype cert = TRUE_CERT of (int * int) * int | FALSE_CERT of (int * int) * int * int
              | ZEROTH_POWER of int | NTH_POWER_EQ_ZERO of int | ZERO_ONE
val mk_cert: int -> int -> cert
val generate_proof: Proof.context -> cert -> thm option

val prove: Proof.context -> int * int -> thm option
val simproc: Proof.context -> Thm.cterm -> thm option

(* helper tools *)
val get_cert_numbers : cert -> int * int

end


structure Is_Nth_Power : IS_NTH_POWER =
struct

val limit = Attrib.setup_config_int \<^binding>\<open>limit\<close> (K 1000000);
exception LIMIT

(*                             n     x     base                  n     x    prime  mult.   *)
datatype cert = TRUE_CERT of (int * int) * int | FALSE_CERT of (int * int) * int * int
              | ZEROTH_POWER of int | NTH_POWER_EQ_ZERO of int | ZERO_ONE

fun parse ct = Tools.parse2 ct @{const_name "is_nth_power"}

fun mk_cert n x =
    if n = 0 then ZEROTH_POWER x else 
    if x = 0 then NTH_POWER_EQ_ZERO n else
    let
        val fs_mset = Algorithms.to_mset (Algorithms.factorize x)
        fun decide acc (n, x) ((p, m)::pms) = 
            if m mod n = 0 then decide ((p, m div n)::acc) (n, x) pms
                           else FALSE_CERT ((n, x), p, m)
          | decide acc (n, x) [] = TRUE_CERT ((n, x), Algorithms.prod_mset acc)
    in
        decide [] (n, x)  fs_mset
    end

exception ERROR
fun generate_proof _ ZERO_ONE =
        @{thm is_zeroth_power_of_1}
            |> SOME
  | generate_proof ctxt (ZEROTH_POWER x) =
        @{thm is_zeroth_power_false}
            |> Drule.infer_instantiate' ctxt [Tools.nat2ct' ctxt x]
            |> Tools.simp ctxt 1
            |> SOME
  | generate_proof ctxt (NTH_POWER_EQ_ZERO n) =
        @{thm is_nth_power_0}
            |> Drule.infer_instantiate' ctxt [Tools.nat2ct' ctxt n]
            |> Tools.simp ctxt 1
            |> SOME
  | generate_proof ctxt (TRUE_CERT ((n, x), base)) =
        @{thm is_nth_power_true}
            |> Drule.infer_instantiate' ctxt
                      (map (Tools.nat2ct' ctxt) [base, n, x])
            |> Tools.simp ctxt 1
            |> SOME
  | generate_proof ctxt (FALSE_CERT ((n, x), p, mult)) =
      let val prime_p = case fst (Pratt.prove_prime [] p ctxt) 
                          of SOME thm => thm |
                                 NONE => raise ERROR
      in
        @{thm is_nth_power_false}
            |> Drule.infer_instantiate' ctxt
                      (map (Tools.nat2ct' ctxt) [p, mult, x div (IntInf.pow (p, mult)), x, n])
            |> (fn thm => thm OF [prime_p])
            |> Tools.simp ctxt 4
            |> SOME
      end

fun prove ctxt (n, x) =               (* term           *)
    (n,x) |-> mk_cert                 (* cert           *)
          |> generate_proof ctxt      (* thm option     *)
    handle ERROR => NONE

fun simproc ctxt input =            (* term            *)
    input |> parse                  (* n, x            *)
          |> (fn (n, x) => if abs x < Config.get ctxt limit then (n, x) else raise LIMIT)
          |> prove ctxt             (* thm option      *)
          |> Tools.wrap             (* thm option      *)
    handle LIMIT => NONE
         | TERM _ => NONE

(* helper tools *)
fun get_cert_numbers ZERO_ONE = (0, 1)
  | get_cert_numbers (ZEROTH_POWER x) = (0, x)
  | get_cert_numbers (NTH_POWER_EQ_ZERO n) = (n, 0)
  | get_cert_numbers (TRUE_CERT ((n, x), _)) = (n, x)
  | get_cert_numbers (FALSE_CERT ((n, x), _, _)) = (n, x)

end
\<close>

simproc_setup is_nth_power_simproc ("is_nth_power (numeral n::nat) (numeral x::nat)") = \<open>K Is_Nth_Power.simproc\<close>

end