module type Theory=sig
  open Fol
  type axiom
  val axiom:axiom->formula
end


module Logic(T : Theory) =
struct
open Fol_u
open Utility
open Fol

module Var_map = Map.Make(String)
module Int_map = Map.Make(struct type t = int let compare : int -> int -> int = compare end)

(**definicja twierdzeń *)
type theorem =
  | Leaf
  | Node of theorem * (formula list) * formula * theorem *theorem
(**tworzenie twierdzenia z aksjomatu *)
let axiom ax=Node(Leaf,[],(T.axiom ax),Leaf,Leaf)

(**wyciąga założenia z twierdzeń *)
let assumptions thm =
  match thm with
  |Leaf->failwith "Not tree"
  |Node(_,xl,_,_,_)->xl
(**zwraca tezę z twierdzenia *)
let consequence thm =
  match thm with
  |Leaf->failwith "Not tree"
  |Node(_,_,x,_,_)->x

(** regułą Ax *)
let by_assumption ff =
  Node(Leaf,(ff::[]),ff,Leaf,Leaf)
(**Wprowadzanie implikacji *)
let imp_i ff thm =
  match thm with
  |Leaf->failwith "empty tree"
  |Node(_,xl,x,_,_)->let newxl=List.fold_right (fun a b->if compare_form a ff then b else a::b) xl [] in
               Node(thm,newxl,Imp(ff,x),Leaf,Leaf)
(**dwie pomocnicze funkcje do list jedna łączy dwie listy pomijając powtarzające się elementy, a druga usuwa element,zdecydowanie lepiej było by to zamienić
na sety*)
let listunion xl yl=
  let newyl=List.fold_right (fun a b-> if List.mem a xl then b else a::b) yl [] in
  List.append xl newyl

let listdelete xl f=
List.fold_right (fun a b-> if compare_form a f then b else a::b) xl []
(**Zasada eliminacji implikacji *)
let imp_e th1 th2 =
  match (th1,th2) with
  |(Node(_,xl,x,_,_),Node(_,yl,y,_,_))->
    (match x with
    |Imp(l,r)->if compare_form l y then Node(th1,(listunion xl yl),r,th2,Leaf) else failwith "wrong arguments"
    |_->failwith "No implication")
  |_->failwith "empty tree"

(**zasada eliminiacji fałszu *)
let bot_e ff thm =
  match thm with
  |Node(_,xl,x,_,_)->if compare_form x False then Node(thm,xl,ff,Leaf,Leaf) else failwith "not false" 
  |_->failwith "wrong theorem"

(**zasada wprowadzania kw. uniwersalnego *)
let all_i thm var=
  match thm with
  |Node(_,xl,x,_,_)-> if List.for_all (fun x->free_variable_in_formula var x) xl 
                    then Node(thm,xl,(bound_variables (All(var,x))),Leaf,Leaf)
                    else failwith "variable is free variable in assumptions"
  |_->failwith "wrong theorem"

(**zasada eliminacji kw. uniwersalnego *)
let all_e thm term=
  match thm with
  |Node(_,xl,form,_,_)->(
    match form with
    |All(x,form1)->Node(thm,xl,(substitute_in_formula x term (bounded_to_free form)),Leaf,Leaf)
    |_->failwith "not quantificator")
  |_->failwith "wrong theorem"

(**zasada wprowadzania koniunkcji *)
let and_i thm1 thm2=
  match (thm1,thm2) with
  |(Node(_,xl,form1,_,_),Node(_,ys,form2,_,_))->
    Node(thm1,(listunion xl ys),(And(form1,form2)),thm2,Leaf)
  |_->failwith "wrong theorems"
(**1 wersja eliminacji koniunckji *)
let and_e1 thm=
  match thm with
  |Node(_,xl,form,_,_)->(
    match form with
    |And(form1,form2)->Node(thm,xl,form1,Leaf,Leaf)
    |_->failwith "not conjunction"
  )
  |_->failwith "wrong theorem"
(**2 wersja eliminacji koniunckji *)
let and_e2 thm=
  match thm with
  |Node(_,xl,form,_,_)->(
    match form with
    |And(form1,form2)->Node(thm,xl,form2,Leaf,Leaf)
    |_->failwith "not conjunction"
  )
  |_->failwith "wrong theorem"
(**wprowadznie prawdy*)
let true_i=Node(Leaf,[],True,Leaf,Leaf)
(**1 wersja wprowadzania alternatywy *)
let or_i1 thm form=
  match thm with
  |Node(_,xl,x,_,_)->Node(thm,xl,Or(x,form),Leaf,Leaf)
  |_->failwith "wrong theorem"
(**2 wersja wprowadzania alternatywy *)
let or_i2 thm form=
  match thm with
  |Node(_,xl,x,_,_)->Node(thm,xl,Or(form,x),Leaf,Leaf)
  |_->failwith "wrong theorem"
(**eliminacja alternatywy *)
let or_e thm1 thm2 thm3=
  match (thm1,thm2,thm3) with
  |(Node(_,xl,form1,_,_),Node(_,ys,form2,_,_),Node(_,zs,form3,_,_))->(
    if compare_form form2 form3 then 
      match form1 with
      |Or(f1,f2)->let yss=listdelete ys f1 in
                  let zss=listdelete zs f2 in
                  Node(thm1,(listunion xl (listunion yss zss)),form2,thm2,thm3)
    |_->failwith "not alternative"
    else failwith "formulas in theorem 2 and theorem 3 are not the same"
  )
  |_->failwith "wrong theorems"
end