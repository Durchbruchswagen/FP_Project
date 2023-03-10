module type Theory=sig
  open Fol
  type axiom
  val axiom:axiom->formula
end

module Proof(T : Theory): sig
open Fol
open Fol_u
open Utility
open Logic.Logic(T)
type proof
type term_v=
  |F_Var_v of string
  |B_Var_v of int
  |Sym_v of string* term_v list 

type formula_v=
  |Leaf_v of term_v
  |False_v
  |True_v
  |Rel_v of string * term_v list
  |Imp_v of formula_v * formula_v
  |And_v of formula_v * formula_v
  |Or_v of formula_v * formula_v
  |Neg_v of formula_v
  |All_v of string * formula_v 

(** Tworzy pusty dowód podanego twierdzenia *)
val proof : (string * formula_u) list -> formula_u -> proof

(** Zamienia ukończony dowód na twierdzenie *)
val qed : proof -> theorem

val see_theorem_u: theorem->formula_u 
val see_theorem : theorem->formula_v
(** Zwraca jeśli dowód jest ukończony, zwraca None. W przeciwnym wypadku
  zwraca Some(assm, phi), gdzie assm oraz phi to odpowiednio dostępne
  założenia oraz formuła do udowodnienia w aktywnym podcelu *)
val goal_u : proof -> ((string * formula_u) list * formula_u) option
val goal : proof -> ((string * formula_v) list * formula_v) option
(** Przesuwa cylkicznie aktywny podcel na następny (od lewej do prawej) *)
val next : proof -> proof

(** Wywołanie intro name pf odpowiada regule wprowadzania implikacji.
  To znaczy aktywna dziura wypełniana jest regułą:

  (nowy aktywny cel)
   (name,ψ) :: Γ ⊢ φ
   -----------------(→I)
       Γ ⊢ ψ → φ

  Jeśli aktywny cel nie jest implikacją, wywołanie kończy się błędem *)
val intro : string -> proof -> proof

(** Wywołanie apply ψ₀ pf odpowiada jednocześnie eliminacji implikacji
  i eliminacji fałszu. Tzn. jeśli do udowodnienia jest φ, a ψ₀ jest
  postaci ψ₁ → ... → ψn → φ to aktywna dziura wypełniana jest regułami
  
  (nowy aktywny cel) (nowy cel)
        Γ ⊢ ψ₀          Γ ⊢ ψ₁
        ----------------------(→E)  (nowy cel)
                ...                   Γ ⊢ ψn
                ----------------------------(→E)
                            Γ ⊢ φ

  Natomiast jeśli ψ₀ jest postaci ψ₁ → ... → ψn → ⊥ to aktywna dziura
  wypełniana jest regułami

  (nowy aktywny cel) (nowy cel)
        Γ ⊢ ψ₀          Γ ⊢ ψ₁
        ----------------------(→E)  (nowy cel)
                ...                   Γ ⊢ ψn
                ----------------------------(→E)
                            Γ ⊢ ⊥
                            -----(⊥E)
                            Γ ⊢ φ *)
val apply : formula_u -> proof -> proof



val apply_thm : theorem -> proof -> proof

val apply_assm : string -> proof -> proof

val alli : proof->string->proof

val alle : proof->formula_u->term_u->proof

val andi : proof->proof

val ande1: proof->formula_u->proof

val ande2: proof->formula_u->proof

val ori1: proof->proof

val ori2: proof->proof

val ore: proof->formula_u->formula_u->proof

val truei: proof->proof

val axi: T.axiom->theorem
end

