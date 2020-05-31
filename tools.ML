signature TOOLS = 
sig

exception MY_INVALID_TERM of term

(* PARSING *)
val parse1: Thm.cterm -> string -> int
val parse2: Thm.cterm -> string -> int * int
val parseZR: Thm.cterm -> string -> int * int    (* second argument is allowed to be *)
                                                 (* int or "real of int" *)

(* CONVERTING VARIABLES TO CTERM OPTIONS FOR INSTANTIATION *)
val nat2ct':  Proof.context -> int -> Thm.cterm option
val real2ct': Proof.context -> int -> Thm.cterm option
val num2ct':  Proof.context -> typ * int -> Thm.cterm option

(* SIMPLIFYING THEOREMS *)
val simp: Proof.context -> int -> thm -> thm
val simp': Proof.context -> int -> thm option -> thm option

(* WRAPPER FOR SIMPROCS *)
val wrap: thm option -> thm option

(* TERM GENERATION *)
val mk_const: Proof.context -> string -> term

(* EXCEPTION HANDLING *)
val LIMIT_and_NONE: string -> thm option
val PARSER_and_NONE: string * term list -> thm option

end

structure Tools : TOOLS = 
struct

exception MY_INVALID_TERM of term

(* PARSING *)
fun parse1 ct str = 
        case Thm.term_of ct 
          of Const (str', _) $ (number) => 
                 if str = str' then snd (HOLogic.dest_number number) 
                               else raise TERM ("parsing error", [Thm.term_of ct])
           | _ => raise TERM ("parsing error", [Thm.term_of ct])
        
fun parse2 ct str = 
        case Thm.term_of ct 
          of Const (str', _) $ (number1) $ (number2) =>
                 if str = str' then (snd (HOLogic.dest_number number1),
                                     snd (HOLogic.dest_number number2))
                               else raise TERM ("parsing error", [Thm.term_of ct])
           | _ => raise TERM ("parsing error", [Thm.term_of ct])

fun parseZR ct str =
        case Thm.term_of ct
          of Const (str', _) $ (number1) $ (Const (@{const_name "of_nat"}, _) $ (number2)) =>
                 if str = str' then (snd (HOLogic.dest_number number1),
                                     snd (HOLogic.dest_number number2))
                               else raise TERM ("parsing error", [Thm.term_of ct])
           | Const (str', _) $ (number1) $ (number2) =>
                 if str = str' then (snd (HOLogic.dest_number number1),
                                     snd (HOLogic.dest_number number2))
                               else raise TERM ("parsing error", [Thm.term_of ct])
           | _ => raise TERM ("parsing error", [Thm.term_of ct])


(* CONVERTING VARIABLES TO CTERM OPTIONS FOR INSTANTIATION *)
fun nat2ct'  ctxt n = SOME (Thm.cterm_of ctxt (HOLogic.mk_number HOLogic.natT n))
fun real2ct' ctxt r = SOME (Thm.cterm_of ctxt (HOLogic.mk_number HOLogic.realT r))
fun num2ct'  ctxt (T, num) = SOME (Thm.cterm_of ctxt (HOLogic.mk_number T num))

(* SIMPLIFYING THEOREMS *)
fun simp _  0 thm = thm
  | simp ctxt n thm = simp ctxt (n-1) (Tactic.rule_by_tactic ctxt (REPEAT_ALL_NEW 
                                    (CHANGED o simp_tac ctxt) 1) thm)
fun simp' ctxt reps thm' = SOME (simp ctxt reps (Option.valOf thm'))

(* WRAPPER FOR SIMPROCS *)
fun wrap NONE = NONE
  | wrap (SOME thm) =
  case Thm.prop_of thm of 
       (Const("HOL.Trueprop", _) $ (Const("HOL.Not", _) $ _)) => SOME (@{thm Eq_FalseI} OF [thm]) |
                                                            _ => SOME (@{thm Eq_TrueI} OF [thm])

(* TERM GENERATION *)
fun mk_const ctxt name = Const (name, Option.valOf (Type_Infer_Context.const_type ctxt name))

(* EXCEPTION HANDLING *)
fun LIMIT_and_NONE simproc_name = 
    let val _ = Pretty.writeln (Pretty.str (simproc_name ^ ".simproc argument out of limits!"))
    in NONE end

fun PARSER_and_NONE (simproc_name, _) =
    let val _ = Pretty.writeln (Pretty.str ("parser error in " ^ simproc_name ^ ".simproc!"))
    in NONE end

end