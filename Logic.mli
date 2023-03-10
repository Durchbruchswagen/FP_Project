module type Theory=sig
  open Fol
  type axiom
  val axiom:axiom->formula
end


module Logic(T : Theory): sig
open Fol_u
open Fol
open Utility
(** reprezentacja twierdzeń *)
type theorem

val axiom: T.axiom->theorem
(** założenia twierdzenia *)
val assumptions : theorem -> formula list
(** teza twierdzenia *)
val consequence : theorem -> formula

(** by_assumption f konstruuje następujący dowód
  -------(Ax)
  {f} ⊢ f  *)
val by_assumption : formula -> theorem

(** imp_i f thm konstruuje następujący dowód

       thm
      Γ ⊢ φ
 ---------------(→I)
 Γ \ {f} ⊢ f → φ *)
val imp_i : formula -> theorem -> theorem

(** imp_e thm1 thm2 konstruuje następujący dowód

    thm1      thm2
 Γ ⊢ φ → ψ    Δ ⊢ φ 
 ------------------(→E)
 Γ ∪ Δ ⊢ ψ *)
val imp_e : theorem -> theorem -> theorem

(** bot_e f thm konstruuje następujący dowód

   thm
  Γ ⊢ ⊥
  -----(⊥E)
  Γ ⊢ f *)
val bot_e : formula -> theorem -> theorem

(**Zasada wprowadzania kwantyfikatora uniwersalnego *)
val all_i : theorem->string->theorem

(**Zasada elminacji kwantyfikatora uniwersalnego *)
val all_e : theorem->term->theorem
(**Zasada wprowadzania koniunkcji *)
val and_i: theorem->theorem->theorem
(**Zasada eliminacji koniunkcji-usuwana formuła po prawej stronie *)
val and_e1: theorem->theorem
(**Zasada eliminacji koniunkcji-usuwana formuła po lewej stronie *)
val and_e2: theorem->theorem
(**Zasada wprowadznia prawdy *)
val true_i: theorem
(**Zasada wprowadzania alternatywy-formuła dodawana po prawej *)
val or_i1: theorem->formula->theorem
(**Zasada wprowadzania alternatywy-formułą dodawana po lewej*)
val or_i2: theorem->formula->theorem
(**Zasada eliminacji alternatywy *)
val or_e: theorem->theorem->theorem->theorem
end