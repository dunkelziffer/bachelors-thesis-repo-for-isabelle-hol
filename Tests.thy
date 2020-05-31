(*  Title:      Tests.thy
    Author:     Klaus Weidinger, TU Muenchen
    Copyright   2020

Tests for all simprocs in Prime, Prime_Factorization, Primepow,
Squarefree2, Is_Nth_Power, Partial_Radication, Coprime and GCD2.
*)

theory Tests
  imports
    Main
    Complex_Main
    "HOL-Computational_Algebra.Primes"
    HOL.Num
    Prime
    Prime_Factorization
    Primepow
    Squarefree2
    Is_Nth_Power
    Partial_Radication
    Coprime
    GCD2
begin

lemma upt_rec_0_numeral [simp]:
  "[0..<numeral n] = 0 # [1..<numeral n]"
  by (subst upt_rec) auto

lemma upt_rec_Suc_0_numeral [simp]:
  "[Suc 0..<numeral n] = (if 1 < (numeral n :: nat) then 1 # [2..<numeral n] else [])"
  by (subst upt_rec) (simp only: One_nat_def numeral_2_eq_2)




text\<open>Prime\<close>

lemma "map prime [0] = [False]"
  by (simp del: prime_nat_numeral_eq not_prime_0)

ML\<open>Prime.simproc @{context} @{cterm "prime (0::nat)"}\<close>

lemma "map prime [1..<(100::nat)] =
    [       False, True, True, False, True, False, True, False, False,
     False, True, False, True, False, False, False, True, False, True,
     False, False, False, True, False, False, False, False, False, True,
     False, True, False, False, False, False, False, True, False, False,
     False, True, False, True, False, False, False, True, False, False,
     False, False, False, True, False, False, False, False, False, True,
     False, True, False, False, False, False, False, True, False, False,
     False, True, False, True, False, False, False, False, False, True,
     False, False, False, True, False, False, False, False, False, True,
     False, False, False, False, False, False, False, True, False, False]"
  by (simp del: prime_nat_numeral_eq not_prime_0 not_prime_1)

lemma "map prime [999980..<(1000000::nat)] =
     [False, False, False, True, False, False, False, False, False, False,
     False, False, False, False, False, False, False, False, False, False]"
  by (simp del: prime_nat_numeral_eq not_prime_0 not_prime_1)




text\<open>Prime_Factorization\<close>

lemma "map prime_factorization [0..<(100::nat)] =
    [{#}, {#}, {#2#}, {#3#}, {#2, 2#}, {#5#}, {#2, 3#}, {#7#}, {#2, 2, 2#}, {#3, 3#},
     {#2, 5#}, {#11#}, {#2, 2, 3#}, {#13#}, {#2, 7#}, {#3, 5#}, {#2, 2, 2, 2#}, {#17#}, {#2, 3, 3#}, {#19#},
     {#2, 2, 5#}, {#3, 7#}, {#2, 11#}, {#23#}, {#2, 2, 2, 3#}, {#5, 5#}, {#2, 13#}, {#3, 3, 3#}, {#2, 2, 7#}, {#29#},
     {#2, 3, 5#}, {#31#}, {#2, 2, 2, 2, 2#}, {#3, 11#}, {#2, 17#}, {#5, 7#}, {#2, 2, 3, 3#}, {#37#}, {#2, 19#}, {#3, 13#},
     {#2, 2, 2, 5#}, {#41#}, {#2, 3, 7#}, {#43#}, {#2, 2, 11#}, {#3, 3, 5#}, {#2, 23#}, {#47#}, {#2, 2, 2, 2, 3#}, {#7, 7#},
     {#2, 5, 5#}, {#3, 17#}, {#2, 2, 13#}, {#53#}, {#2, 3, 3, 3#}, {#5, 11#}, {#2, 2, 2, 7#}, {#3, 19#}, {#2, 29#}, {#59#},
     {#2, 2, 3, 5#}, {#61#}, {#2, 31#}, {#3, 3, 7#}, {#2, 2, 2, 2, 2, 2#}, {#5, 13#}, {#2, 3, 11#}, {#67#}, {#2, 2, 17#}, {#3, 23#},
     {#2, 5, 7#}, {#71#}, {#2, 2, 2, 3, 3#}, {#73#}, {#2, 37#}, {#3, 5, 5#}, {#2, 2, 19#}, {#7, 11#}, {#2, 3, 13#}, {#79#},
     {#2, 2, 2, 2, 5#}, {#3, 3, 3, 3#}, {#2, 41#}, {#83#}, {#2, 2, 3, 7#}, {#5, 17#}, {#2, 43#}, {#3, 29#}, {#2, 2, 2, 11#}, {#89#},
     {#2, 3, 3, 5#}, {#7, 13#}, {#2, 2, 23#}, {#3, 31#}, {#2, 47#}, {#5, 19#}, {#2, 2, 2, 2, 2, 3#}, {#97#}, {#2, 7, 7#}, {#3, 3, 11#}]"
  by (simp del: prime_factorization_0 prime_factorization_1 prime_factorization_normalize
                prime_factorization_subset_iff_dvd prime_factorization_divide
                prime_factorization_gcd_factorial prime_factorization_lcm_factorial
                prime_factorization_gcd prime_factorization_lcm)

lemma "map prime_factorization [999980..<(1000000::nat)] =
    [{#2, 2, 5, 49999#}, {#3, 3, 111109#}, {#2, 79, 6329#}, {#999983#}, {#2, 2, 2, 2, 3, 83, 251#},
     {#5, 7, 28571#}, {#2, 13, 38461#}, {#3, 257, 1297#}, {#2, 2, 11, 22727#}, {#19, 52631#},
     {#2, 3, 3, 5, 41, 271#}, {#17, 59, 997#}, {#2, 2, 2, 7, 7, 2551#}, {#3, 333331#}, {#2, 23, 21739#},
     {#5, 199999#}, {#2, 2, 3, 167, 499#}, {#757, 1321#}, {#2, 31, 127, 127#}, {#3, 3, 3, 7, 11, 13, 37#}]"
  by (simp del: prime_factorization_0 prime_factorization_1 prime_factorization_normalize
                prime_factorization_subset_iff_dvd prime_factorization_divide
                prime_factorization_gcd_factorial prime_factorization_lcm_factorial
                prime_factorization_gcd prime_factorization_lcm)




text\<open>Primepow\<close>

lemma "map primepow [0..<(100::nat)] =
    [False, False, True, True, True, True, False, True, True, True,
     False, True, False, True, False, False, True, True, False, True,
     False, False, False, True, False, True, False, True, False, True,
     False, True, True, False, False, False, False, True, False, False,
     False, True, False, True, False, False, False, True, False, True,
     False, False, False, True, False, False, False, False, False, True,
     False, True, False, False, True, False, False, True, False, False,
     False, True, False, True, False, False, False, False, False, True,
     False, True, False, True, False, False, False, False, False, True,
     False, False, False, False, False, False, False, True, False, False]"
  by (simp del: zero_not_primepow one_not_primepow primepow_not_unit 
                not_primepow_Suc_0_nat primepow_prime primepow_prime_power)

lemma "map primepow [999980..<(1000000::nat)] =
    [False, False, False, True, False, False, False, False, False, False,
     False, False, False, False, False, False, False, False, False, False]"
  by (simp del: zero_not_primepow one_not_primepow primepow_not_unit 
                not_primepow_Suc_0_nat primepow_prime primepow_prime_power)




text\<open>Squarefree2\<close>

lemma "map squarefree [0..<(100::nat)] =
    [False, True, True, True, False, True, True, True, False, False,
     True, True, False, True, True, True, False, True, False, True,
     False, True, True, True, False, False, True, False, False, True,
     True, True, False, True, True, True, False, True, True, True,
     False, True, True, True, False, False, True, True, False, False,
     False, True, False, True, False, True, False, True, True, True,
     False, True, True, False, False, True, True, True, False, True,
     True, True, False, True, True, False, False, True, True, True,
     False, False, True, True, False, True, True, True, False, True,
     False, True, False, True, True, True, False, True, False, False]"
  by (simp del: not_squarefree_0 squarefree_unit squarefree_1
                squarefree_minus)

lemma "map squarefree [999980..<(1000000::nat)] =
    [False, False, True, True, False, True, True, True, False, True,
     False, True, False, True, True, True, False, True, False, False]"
  by (simp del: not_squarefree_0 squarefree_unit squarefree_1
                squarefree_minus)




text\<open>Is_Nth_Power\<close>

lemma "List.bind [0..<10] (\<lambda>a. map (is_nth_power a) [0..<10]) =
    [False, True, False, False, False, False, False, False, False, False,
     True, True, True, True, True, True, True, True, True, True,
     True, True, False, False, True, False, False, False, False, True,
     True, True, False, False, False, False, False, False, True, False,
     True, True, False, False, False, False, False, False, False, False,
     True, True, False, False, False, False, False, False, False, False,
     True, True, False, False, False, False, False, False, False, False,
     True, True, False, False, False, False, False, False, False, False,
     True, True, False, False, False, False, False, False, False, False,
     True, True, False, False, False, False, False, False, False, False]"
  by (simp add: List.bind_def
           del: is_nth_power_nth_power is_zeroth_power is_first_power
                is_first_power' is_nth_power_0 is_nth_power_0_iff
                is_nth_power_1 is_nth_power_Suc_0)

lemma "List.bind [0..<10] (\<lambda>a. map (is_nth_power a) [99990..<100010]) =
    [False, False, False, False, False, False, False, False, False, False,
     False, False, False, False, False, False, False, False, False, False,

     True, True, True, True, True, True, True, True, True, True,
     True, True, True, True, True, True, True, True, True, True,

     False, False, False, False, False, False, False, False, False, False,
     False, False, False, False, False, False, False, False, False, False,

     False, False, False, False, False, False, False, False, False, False,
     False, False, False, False, False, False, False, False, False, False,

     False, False, False, False, False, False, False, False, False, False,
     False, False, False, False, False, False, False, False, False, False,

     False, False, False, False, False, False, False, False, False, False,
     True, False, False, False, False, False, False, False, False, False,

     False, False, False, False, False, False, False, False, False, False,
     False, False, False, False, False, False, False, False, False, False,

     False, False, False, False, False, False, False, False, False, False,
     False, False, False, False, False, False, False, False, False, False,

     False, False, False, False, False, False, False, False, False, False,
     False, False, False, False, False, False, False, False, False, False,

     False, False, False, False, False, False, False, False, False, False,
     False, False, False, False, False, False, False, False, False, False]"
  by (simp add: List.bind_def
           del: is_nth_power_nth_power is_zeroth_power is_first_power
                is_first_power' is_nth_power_0 is_nth_power_0_iff
                is_nth_power_1 is_nth_power_Suc_0)




text\<open>Partial_Radication\<close>

lemma "List.bind [0..<10] (\<lambda>a. map (root a) [0..<10]) =
     foo"
  apply (simp add: List.bind_def
              del: root_0 real_root_zero real_root_one real_root_Suc_0)

lemma "List.bind [0..<10] (\<lambda>a. map (root a) [999990..<1000000]) =
     foo"
  apply (simp add: List.bind_def
              del: root_0 real_root_zero real_root_one real_root_Suc_0)




text\<open>Coprime\<close>

lemma "List.bind [0..<10] (\<lambda>a. map (coprime a) [0..<10]) =
     [False, True, False, False, False, False, False, False, False, False,
     True, True, True, True, True, True, True, True, True, True,
     False, True, False, True, False, True, False, True, False, True,
     False, True, True, False, True, True, False, True, True, False,
     False, True, False, True, False, True, False, True, False, True,
     False, True, True, True, True, False, True, True, True, True,
     False, True, False, False, False, True, False, True, False, False,
     False, True, True, True, True, True, True, False, True, True,
     False, True, False, True, False, True, False, True, False, True,
     False, True, True, False, True, True, False, True, True, False]"
  by (simp add: List.bind_def)

lemma "List.bind [1000..<1010] (\<lambda>a. map (coprime a) [999990..<1000000]) =
     [False, True, False, True, False, False, False, True, False, True,
     True, True, False, True, True, True, True, True, True, False,
     False, True, False, False, False, True, False, True, False, False,
     True, False, True, True, True, True, True, True, True, True,
     False, True, False, True, False, True, False, True, False, True,
     False, True, True, False, True, False, False, True, True, False,
     False, True, False, True, False, True, False, True, False, True,
     True, True, True, True, True, True, True, True, True, True,
     False, True, False, False, False, True, False, True, False, False,
     True, True, True, True, True, True, True, True, True, True]"
  by (simp add: List.bind_def)




text\<open>GCD2\<close>

lemma "List.bind [0..<10] (\<lambda>a. map (gcd a) [0..<10]) =
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
     1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
     2, 1, 2, 1, 2, 1, 2, 1, 2, 1,
     3, 1, 1, 3, 1, 1, 3, 1, 1, 3,
     4, 1, 2, 1, 4, 1, 2, 1, 4, 1,
     5, 1, 1, 1, 1, 5, 1, 1, 1, 1,
     6, 1, 2, 3, 2, 1, 6, 1, 2, 3,
     7, 1, 1, 1, 1, 1, 1, 7, 1, 1,
     8, 1, 2, 1, 4, 1, 2, 1, 8, 1,
     9, 1, 1, 3, 1, 1, 3, 1, 1, 9]"
  by (simp add: List.bind_def)

lemma "List.bind [1000..<1010] (\<lambda>a. map (gcd a) [999980..<1000000]) =
    [20, 1, 2, 1, 8, 5, 2, 1, 4, 1,
     10, 1, 8, 1, 2, 5, 4, 1, 2, 1,
     1, 1, 1, 1, 1, 7, 13, 1, 11, 1,
     1, 1, 7, 1, 1, 1, 1, 1, 1, 1001,
     2, 3, 2, 1, 6, 1, 2, 3, 2, 1,
     6, 1, 2, 3, 2, 1, 1002, 1, 2, 3,
     1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
     1, 1003, 1, 1, 1, 1, 1, 1, 1, 1,
     4, 1, 2, 1, 1004, 1, 2, 1, 4, 1,
     2, 1, 4, 1, 2, 1, 4, 1, 2, 1,
     5, 3, 1, 1, 3, 5, 1, 3, 1, 1,
     15, 1, 1, 3, 1, 5, 3, 1, 1, 3,
     2, 1, 2, 1, 2, 1, 2, 1, 2, 1,
     2, 1, 2, 1, 2, 1, 2, 1, 2, 1,
     1, 1, 1, 1, 1, 1, 1, 1, 1, 19,
     1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
     4, 9, 2, 1, 48, 7, 2, 3, 4, 1,
     18, 1, 56, 3, 2, 1, 12, 1, 2, 63,
     1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
     1, 1, 1, 1, 1, 1, 1, 1, 1, 1]"
  by (simp add: List.bind_def)

end