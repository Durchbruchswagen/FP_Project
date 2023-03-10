module type Theory=sig
  open Fol
  type axiom
  val axiom:axiom->formula
end
module Proof(T : Theory) =
struct
open Fol
open Fol_u
open Utility
open Logic.Logic(T)

type osad = (string * formula) list * formula

type proof_tree =
  | Ax of theorem
  | ImpI of proof_tree * osad
  | ImpE of proof_tree * osad * proof_tree
  | BotE of proof_tree * osad
  | AllI of proof_tree * osad
  | AllE of proof_tree * osad * term
  | AndI of proof_tree * osad * proof_tree
  | AndE1 of proof_tree * osad
  | AndE2 of proof_tree * osad
  | OrI1 of proof_tree * osad
  | OrI2 of proof_tree * osad
  | OrE of proof_tree * osad * proof_tree * proof_tree
  | Goal of (string * formula) list * formula

type proof_tree_context =
  | Root
  | Ctx_bote of proof_tree_context * osad
  | Ctx_impi of proof_tree_context * osad
  | Left_impe of proof_tree_context * osad * proof_tree
  | Right_impe of proof_tree * osad * proof_tree_context
  | Ctx_alli of proof_tree_context * osad
  | Ctx_alle of proof_tree_context * osad * term
  | Left_andi of proof_tree_context * osad * proof_tree
  | Right_andi of proof_tree * osad * proof_tree_context
  | Ctx_ande1 of proof_tree_context * osad
  | Ctx_ande2 of proof_tree_context * osad
  | Ctx_ori1 of proof_tree_context * osad
  | Ctx_ori2 of proof_tree_context * osad
  | Left_orie of proof_tree_context * osad * proof_tree * proof_tree
  | Middle_orie of proof_tree * osad * proof_tree_context * proof_tree
  | Right_orie of proof_tree * osad * proof_tree * proof_tree_context

type proof =
  | Incomplete of proof_tree * proof_tree_context
  | Complete of theorem
(**widok dla formuł z częściowymi indeksami *)
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

(**zamiana formuł z częściowymi indeksami na widoki *)
let rec create_v_t term=
  match term with
  |F_Var(s1)->F_Var_v(s1)
  |B_Var(n)->B_Var_v(n)
  |Sym(s1,xs)->Sym_v(s1,List.map create_v_t xs)
                 
let rec create_v form=
  match form with 
  |Leaf(t)->Leaf_v(create_v_t t)
  |False->False_v
  |True->True_v
  |Rel(sym,xs)->Rel_v(sym,(List.map create_v_t xs))
  |Imp(f1,f2)->Imp_v((create_v f1),(create_v f2))
  |And(f1,f2)->And_v((create_v f1),(create_v f2))
  |Or(f1,f2)->Or_v((create_v f1),(create_v f2))
  |Neg(f1)->Neg_v(create_v f1)
  |All(s1,f1)->All_v(s1,(create_v f1) )

(**tworzenie dowodu *)
let proof g f = 
  let gg=List.map (fun x->((fst x),(de_brujin (snd x)))) g in
  let ff=de_brujin f in
  Incomplete (Goal (gg, ff), Root)
(**zamiana dowodu na twierdzenie *)
let qed pf =
  match pf with
  | Incomplete (_, _) -> failwith "Incomplete proof"
  | Complete thm -> thm
(**wypisanie aktualnego celu jako widok lub formuła bez indeksów *)
let goal_u pf =
  match pf with
  | Incomplete (t, _) -> (
      match t with
      | Goal (g, f) -> let gg=List.map (fun x->((fst x),(de_de_brujin (snd x)))) g in
                       let ff=de_de_brujin f in
                       Option.Some (gg, ff)
      | _ -> failwith "Error, not a goal")
  | Complete _ -> Option.None

let goal pf =
  match pf with
  | Incomplete (t, _) -> (
      match t with
      | Goal (g, f) ->let gg=List.map (fun x->((fst x),(create_v (snd x)))) g in
                       let ff=create_v f in
                       Option.Some (gg, ff)
      | _ -> failwith "Error, not a goal")
  | Complete _ -> Option.None
(**to samo co wyżej tylko, że dla twierdzeń *)
let see_theorem_u thm=de_de_brujin (consequence thm)
let see_theorem thm=create_v (consequence thm)
(**funkcja która idzie w górę drzewa dopóki nie dojdzie do miejsca gdzie może skręcić w prawo lub nie dotrze do korzenia *)
let rec search_up (t, ctx) =
  match ctx with
  | Root -> ((t, ctx), "r")
  | Ctx_bote (ctx, a) -> search_up (BotE (t, a), ctx)
  | Ctx_impi (ctx, a) -> search_up (ImpI (t, a), ctx)
  | Left_impe (ctx, a, r) -> ((ImpE (t, a, r), ctx), "l")
  | Right_impe (l, a, ctx) -> search_up (ImpE (l, a, t), ctx)
  | Ctx_alli (ctx,a)-> search_up (AllI(t,a),ctx)
  | Ctx_alle (ctx,a,te)-> search_up (AllE(t,a,te),ctx)
  | Left_andi (ctx,a,r)->((AndI(t,a,r),ctx),"l")
  | Right_andi (l,a,ctx)->search_up (AndI(l,a,t),ctx)
  | Ctx_ande1 (ctx,a)->search_up (AndE1(t,a),ctx)
  | Ctx_ande2 (ctx,a)->search_up (AndE2(t,a),ctx)
  | Ctx_ori1 (ctx,a)->search_up (OrI1(t,a),ctx) 
  | Ctx_ori2 (ctx,a)->search_up (OrI2(t,a),ctx)
  | Left_orie (ctx,a,m,r)->((OrE(t,a,m,r),ctx),"l")
  | Middle_orie (l,a,ctx,r)->((OrE(l,a,t,r),ctx),"m")
  | Right_orie (l,a,m,ctx)->search_up (OrE(l,a,m,t),ctx)
(**funkcja idzie w dół drzewa w poszukiwaniu celu *)
let rec search_down ((t, ctx), dir) =
  match t with
  | Ax _ -> Option.None
  | ImpI (t, a) -> search_down ((t, Ctx_impi (ctx, a)), "r")
  | ImpE (l, a, r) ->
      let vleft = search_down ((l, Left_impe (ctx, a, r)), "r") in
      let vright = search_down ((r, Right_impe (l, a, ctx)), "r") in
      if dir = "l" then vright
      else if Option.is_some vleft then vleft
      else vright
  | BotE (t, a) -> search_down ((t, Ctx_bote (ctx, a)), "r")
  | Goal (_, _) -> Option.Some (Incomplete (t, ctx))
  | AllI (t,a)-> search_down ((t, Ctx_alli (ctx,a)),"r")
  | AllE (t,a,ter)-> search_down ((t, Ctx_alle (ctx,a,ter)),"r")
  | AndI (l,a,r)->
      let vleft=search_down ((l,Left_andi (ctx,a,r)),"r") in
      let vright=search_down ((r,Right_andi(l,a,ctx)),"r") in
      if dir = "l" then vright
      else if Option.is_some vleft then vleft else vright
  | AndE1 (t,a)-> search_down ((t,Ctx_ande1(ctx,a)),"r")
  | AndE2 (t,a)-> search_down ((t,Ctx_ande2(ctx,a)),"r")
  | OrI1 (t,a)-> search_down ((t,Ctx_ori1(ctx,a)),"r")
  | OrI2 (t,a)-> search_down ((t,Ctx_ori2(ctx,a)),"r")
  | OrE (l,a,m,r)->
      let vleft=search_down ((l,Left_orie (ctx,a,m,r)),"r") in
      let vmidle=search_down ((m,Middle_orie(l,a,ctx,r)),"r") in
      let vright=search_down ((r,Right_orie(l,a,m,ctx)),"r") in
      if dir = "l" then (if Option.is_some vmidle then vmidle else vright)
      else if dir="m" then vright else (if Option.is_some vleft then vleft else (if Option.is_some vmidle then vmidle else vright))

(**szukanie kolejnego celu *)
let next pf =
  match pf with
  | Complete _ -> failwith "No goals, proof is complete"
  | Incomplete (t, ctx) ->
      let rec help (a, b) =
        let check = search_up (a, b) in
        let value = search_down (check) in
        if Option.is_some value then Option.get value else help (fst check)
      in
      help (t, ctx)
(**działa intro oraz apply jest opsiane w pliku mli *)
let intro name pf =
  match pf with
  | Complete _ -> failwith "proof is complete"
  | Incomplete (t, ctx) -> (
      match t with
      | Goal (formxs, form) -> (
          match form with
          | Imp (t1, t2) ->
              Incomplete
                (Goal ((name, t1) :: formxs, t2), Ctx_impi (ctx, (formxs, form)))
          | _ -> failwith "wrong formula")
      | _ -> failwith "Not goal")

let getformula t = match t with Goal (xl, f) -> f | _ -> failwith "Not goal"

(**pomocnicza formuła do apply która zamienia ciąg implikcaji na listę formuł*)
let rec getlist f fcomp xl =
  match f with
  | Imp (t1, t2) -> if compare_form t2 fcomp then t1 :: xl else getlist t2 fcomp (t1 :: xl)
  | False -> False :: xl
  | _-> if compare_form f fcomp then xl else failwith "wrong formula in getlist"

(**pomocnicza formuła która tworzy kolejne fragmenty drzewa z regułu wpr. implikacji dopóki tablica xl nie jest pusta *)
let rec create_imp_i formxs xl form (t, ctx) =
  match xl with
  | [] -> Incomplete (t, ctx)
  | x :: xs -> (
      match x with
      | False ->
          create_imp_i formxs xs False
            (Goal (formxs, False), Ctx_bote (ctx, (formxs, form)))
      | Imp (_, _) ->
          create_imp_i formxs xs
            (Imp (x, form))
            ( Goal (formxs, Imp (x, form)),
              Left_impe (ctx, (formxs, form), Goal (formxs, x)) )
      | _ ->
          create_imp_i formxs xs
            (Imp (x, form))
            ( Goal (formxs, Imp (x, form)),
              Left_impe (ctx, (formxs, form), Goal (formxs, x)) ))
      
let check_if_imp f =
  match f with Imp(_,_)->true | _->false

let apply ff pf =
  let f=de_brujin ff in
  match pf with
  | Complete _ -> failwith "complete proof"
  | Incomplete (t, ctx) -> (
      match t with
      | Goal (formxs, form) ->
          if check_if_imp f then
            create_imp_i formxs (getlist f form []) form (t, ctx)
          else failwith "not implication"
      | _ -> failwith "Not goal")

let go_up (t, ctx) =
  match ctx with
  | Root -> (t, ctx)
  | Ctx_bote (ctx, a) -> (BotE (t, a), ctx)
  | Ctx_impi (ctx, a) -> (ImpI (t, a), ctx)
  | Left_impe (ctx, a, r) -> (ImpE (t, a, r), ctx)
  | Right_impe (l, a, ctx) -> (ImpE (l, a, t), ctx)
  | Ctx_alli (ctx,a)->(AllI(t,a),ctx)
  | Ctx_alle (ctx,a,ter)-> (AllE(t,a,ter),ctx)
  | Left_andi (ctx,a,r)->(AndI(t,a,r),ctx)
  | Right_andi (l,a,ctx)->(AndI(l,a,t),ctx)
  | Ctx_ande1 (ctx,a)->(AndE1(t,a),ctx)
  | Ctx_ande2 (ctx,a)->(AndE2(t,a),ctx)
  | Ctx_ori1 (ctx,a)->(OrI1(t,a),ctx) 
  | Ctx_ori2 (ctx,a)->(OrI2(t,a),ctx)
  | Left_orie (ctx,a,m,r)->(OrE(t,a,m,r),ctx)
  | Middle_orie (l,a,ctx,r)->(OrE(l,a,t,r),ctx)
  | Right_orie (l,a,m,ctx)->(OrE(l,a,m,t),ctx)

let check_if_ax t = match t with Ax _ -> true | _ -> false

let get_thoeorem t = match t with Ax a -> a | _ -> failwith "Not Ax"

let get_quantified_variable t= match t with All(str,f)->str | _-> failwith "Not All"

let or1help os=match (snd os) with
  |Or(f1,f2)->f2
  |_->failwith "not alternative"

let or2help os=match (snd os) with
  |Or(f1,f2)->f1
  |_->failwith "not alternative"

let impi_help t =
  match t with Imp (t1, t2) -> t1 | _ -> failwith "not implication"
(**zamienia (jeżeli możę), kawałek drzewa na twierdzenie *)
let rec turn_into_theorem (t, ctx) =
  match t with
  | Ax thm -> (
      match ctx with
      | Root -> Complete thm
      | _ -> turn_into_theorem (go_up (t, ctx)))
  | ImpI (t, os) ->
      if check_if_ax t then
        turn_into_theorem
          (go_up (Ax (imp_i (impi_help (snd os)) (get_thoeorem t)), ctx))
      else Incomplete (t, ctx)
  | ImpE (t1, os, t2) ->
      if check_if_ax t1 && check_if_ax t2 then
        turn_into_theorem
          (go_up (Ax (imp_e (get_thoeorem t1) (get_thoeorem t2)), ctx))
      else Incomplete (t, ctx)
  | BotE (t, os) ->
      if check_if_ax t then
        turn_into_theorem (go_up (Ax (bot_e (snd os) (get_thoeorem t)), ctx))
      else Incomplete (t, ctx)
  | AllI (t,os)->
    if check_if_ax t then
      turn_into_theorem (go_up (Ax (all_i (get_thoeorem t) (get_quantified_variable (snd os))), ctx))
    else Incomplete (t,ctx) 
  | AllE (t,os,ter)->
    if check_if_ax t then
      turn_into_theorem (go_up (Ax (all_e (get_thoeorem t) ter),ctx))
    else Incomplete (t,ctx)
  | AndI (l,os,r)->
      if check_if_ax l && check_if_ax r then
        turn_into_theorem
          (go_up (Ax (and_i (get_thoeorem l) (get_thoeorem r)), ctx))
      else Incomplete (t,ctx)
  | AndE1 (t,os)->
    if check_if_ax t then
      turn_into_theorem (go_up (Ax (and_e1 (get_thoeorem t)),ctx))
    else Incomplete (t, ctx)
  | AndE2 (t,os)->
    if check_if_ax t then
      turn_into_theorem (go_up (Ax (and_e2 (get_thoeorem t)),ctx))
    else Incomplete (t, ctx)
  | OrI1 (t,os)->
    if check_if_ax t then
      turn_into_theorem (go_up (Ax (or_i1 (get_thoeorem t) (or1help os)),ctx))
    else Incomplete (t, ctx)
  | OrI2 (t,os)->
    if check_if_ax t then
      turn_into_theorem (go_up (Ax (or_i2 (get_thoeorem t) (or2help os)),ctx))
    else Incomplete (t, ctx)
  |OrE (l,os,m,r)->
    if check_if_ax l && check_if_ax m && check_if_ax r then
      turn_into_theorem (go_up (Ax (or_e (get_thoeorem l) (get_thoeorem m) (get_thoeorem r)),ctx))
    else Incomplete(t,ctx)
  | _ -> failwith "Cannot turn goal into theorem"

(**funkcja sprawdza czy założenia się zgadzają *)
let check_assumptions formxs xl=
  let formx=List.fold_right (fun a b-> (snd a)::b) formxs [] in
  List.for_all (fun x->List.mem x formx) xl

(**aplikuje twierdzenie do aktualnego celu *)
let app thm pf =
  match pf with
  | Complete _ -> failwith "Proof complete"
  | Incomplete (t, ctx) -> (
      match t with
      | Goal (formxs, form) ->
          if compare_form form (consequence thm) then (if check_assumptions formxs (assumptions thm) then (Ax thm, ctx) else failwith "wrong assumptions")
          else failwith "thm and formula are not equal"
      | _ -> failwith "Not goal,cannot apply theorem")
(**aplikuje twierdzenie do celu i zamienia kawałek drzewa na twierdzenie, a następnie znajduje nowy cel *)
let apply_thm thm pf =
  let x = turn_into_theorem (app thm pf) in
  match x with
  | Complete _ -> x
  | Incomplete (t, ctx) ->
      let firstsearch = search_down ((t, ctx), "r") in
      if Option.is_some firstsearch then Option.get firstsearch else next x
(**podobnie jak wyżej tylko zamiast twierdzenia używamy założenia *)
let get_from_assumption name pf =
  match pf with
  | Complete _ -> failwith "proof complete"
  | Incomplete (t, ctx) -> (
      match t with
      | Goal (formxs, form) -> by_assumption (List.assoc name formxs)
      | _ -> failwith "Get_from_assumption: not goal")

let apply_assm name pf =
  let x = turn_into_theorem (app (get_from_assumption name pf) pf) in
  match x with
  | Complete _ -> x
  | Incomplete (t, ctx) ->
      let firstsearch = search_down ((t, ctx), "r") in
      if Option.is_some firstsearch then Option.get firstsearch else next x
(**Niżej są definicje zasad jakich używa użytkownik, nazwy są zbliżone do tego co jest w module Logic, tylko bez podłogi *)
let alli proof var=
  match proof with
  |Complete(_)->failwith "Proof complete"
  |Incomplete(t,ctx)->
    match t with
    |Goal(xs,f)->(
      match f with
      |All(x,f1)->if List.for_all (fun x->free_variable_in_formula var (snd x)) xs 
      then Incomplete ((Goal(xs,(bounded_to_free (All(var,f1))))),Ctx_alli(ctx,(xs,f)))
      else failwith "var is free in assumptions"
      |_-> failwith "wrong formula")
    |_-> failwith "not goal"



(** tutaj użytkowni podaje formułe która zaczyna się od kwantyfikatora uniw. następnie kwantyfikator jest usuwany oraz za zmienną kwantyfikowaną 
jest podstawiany term i sprawdzamy czy formuły się zgadzają *)
let alle proof form term=
  let var=match (de_brujin form) with
    |All(s1,_)->s1;
    |_->failwith "not All" in
  let ter=de_brujin_term term in
  let fform=bounded_to_free (de_brujin form) in
  match proof with
  |Complete(_)->failwith "Proof complete"
  |Incomplete(t,ctx)->
    match t with
    |Goal(xs,f)->(
      if compare_form f (substitute_in_formula var ter fform) then 
      Incomplete ((Goal(xs,(de_brujin form))),Ctx_alle(ctx,(xs,f),ter)) else failwith "wrong substitution")
    |_-> failwith "not goal"

let andi proof =
  match proof with
  |Complete(_)->failwith "Proof complete"
  |Incomplete(t,ctx)->
    match t with
    |Goal(xs,f)->(
      match f with
      |And(f1,f2)->Incomplete ((Goal(xs,f1)),Left_andi(ctx,(xs,f),Goal(xs,f2)))
      |_-> failwith "Not conjunction")
    |_-> failwith "not goal"

let ande1 proof form=
  let ff=de_brujin form in
  match proof with
  |Complete(_)->failwith "Proof complete"
  |Incomplete(t,ctx)->
    match t with
    |Goal(xs,f)->
      Incomplete ((Goal(xs,And(f,ff))),Ctx_ande1(ctx,(xs,f)))
    |_-> failwith "not goal"

let ande2 proof form=
  let ff=de_brujin form in
  match proof with
  |Complete(_)->failwith "Proof complete"
  |Incomplete(t,ctx)->
    match t with
    |Goal(xs,f)->
      Incomplete ((Goal(xs,And(ff,f))),Ctx_ande2(ctx,(xs,f)))
    |_-> failwith "not goal"

let ori1 proof=
  match proof with
  |Complete(_)->failwith "Proof complete"
  |Incomplete(t,ctx)->
    match t with
    |Goal(xs,f)->(
      match f with
      |Or(f1,f2)->Incomplete ((Goal(xs,f1)),Ctx_ori1(ctx,(xs,f)))
      |_->failwith "not alternative")
    |_-> failwith "not goal"

let ori2 proof=
  match proof with
  |Complete(_)->failwith "Proof complete"
  |Incomplete(t,ctx)->
    match t with
    |Goal(xs,f)->(
      match f with
      |Or(f1,f2)->Incomplete ((Goal(xs,f2)),Ctx_ori1(ctx,(xs,f)))
      |_->failwith "not alternative")
    |_-> failwith "not goal"

let listdelete xl f=
List.fold_right (fun a b-> if compare_form (snd a) f then b else a::b) xl []

let ore proof f1 f2=
  let ff1=de_brujin f1 in
  let ff2=de_brujin f2 in
  match proof with
  |Complete(_)->failwith "Proof complete"
  |Incomplete(t,ctx)->
    match t with
    |Goal(xs,f)->
      let xs1=listdelete xs ff1 in
      let xs2=listdelete xs ff2 in
      Incomplete ((Goal(xs,Or(ff1,ff2))),Left_orie(ctx,(xs,f),Goal(xs1,f),Goal(xs2,f)))
    |_-> failwith "not goal"

let check_if_top pf=
  match pf with
  |Complete(_)->failwith "Proof complete"
  |Incomplete(t,ctx)->
    match t with
    |Goal(xs,f)->(
      match f with
      |True->(Ax(true_i),ctx)
      |_->failwith "not true")
    |_-> failwith "not goal"

let truei proof=
  let x = turn_into_theorem (check_if_top proof) in
  match x with
  | Complete _ -> x
  | Incomplete (t, ctx) ->
      let firstsearch = search_down ((t, ctx), "r") in
      if Option.is_some firstsearch then Option.get firstsearch else next x

let axi ax=axiom ax
end