open Fol
open Fol_u

module Var_map = Map.Make(String)
module Int_map = Map.Make(struct type t = int let compare : int -> int -> int = compare end)
(**Sprawdź czy zmienna termowa jest liczbą *)
let is_int s =
  try ignore (int_of_string s); true
  with _ -> false
 
let is_float s =
  try ignore (float_of_string s); true
  with _ -> false
 
let is_numeric s = is_int s || is_float s

(**Sprawdzanie czy dwie listy są takie samie, jest to w ocamlu, ale niestety nie w wersji którą posiadam*)
let equal pred xs ys=
  let rec help xs ys=
  match (xs,ys) with
    |(x::xx,y::yy)-> if pred x y then help xx yy else false
    |([],[])-> true
    |_->false in
  if (List.compare_lengths xs ys)<>0 then false else help xs ys


(**zamiana formuły napisanej przez użytkowania na formułę z częściowymi indeksami.*)
let rec db_term t map_var k=
  match t with
  |Var_u(str)->if is_numeric str then failwith "variable name cannot be numeric" else 
      if Var_map.mem str map_var then B_Var(k-(Var_map.find str map_var)) else F_Var(str)
  |Sym_u(str,xs)->Sym(str,(List.map (fun t->db_term t map_var k) xs))

let rec de_brujin_term t=db_term t Var_map.empty 0

let de_brujin f= 
  let rec help f map_var k= 
    match f with
    |Leaf_u(t)->Leaf(db_term t map_var k)
    |False_u->False 
    |True_u->True
    |Rel_u(s1,xs)->Rel(s1,(List.map (fun x->db_term x map_var k) xs))
    |Imp_u(f1,f2)->Imp((help f1 map_var k),(help f2 map_var k))
    |And_u(f1,f2)->And((help f1 map_var k),(help f2 map_var k))
    |Or_u(f1,f2)->Or((help f1 map_var k),(help f2 map_var k))
    |Neg_u(f)->Neg(help f map_var k)
    |All_u(str,f)->All(str,(help f (Var_map.add str k map_var) (k+1))) in
  help f Var_map.empty 0
  
    
(**Pomocnicza funkcja do sprawdzania czy nowo wygenerowana zmienna jest "świeża" *)
let is_fresh_one s f=
  let rec is_fresh_term t=
    match t with
    |F_Var(s1)->if s=s1 then false else true
    |B_Var(s1)->true
    |Sym(sym,xs)->List.for_all is_fresh_term xs in
  let rec is_fresh_formula f=
    match f with
    |Leaf(t)->is_fresh_term t
    |False->true 
    |True->true
    |Rel(s1,xs)->List.for_all is_fresh_term xs
    |Imp(f1,f2)->(is_fresh_formula f1) && (is_fresh_formula f2)
    |And(f1,f2)->(is_fresh_formula f1) && (is_fresh_formula f2)
    |Or(f1,f2)->(is_fresh_formula f1) && (is_fresh_formula f2)
    |Neg(f1)->(is_fresh_formula f1)
    |All(s1,f2)->(s1 <> s) && (is_fresh_formula f2) in
  is_fresh_formula f 
    
let is_fresh_list s xl=
  List.for_all (fun x->is_fresh_one s x) xl

(**generowanie świeżej zmiennej, tablica xl to tablica formuł dla których zmienna ma być świeża*)  
let fresh_var xl=
  let rec help n=
    if is_fresh_list ("fr" ^ string_of_int n) xl then "fr" ^ string_of_int n else help (n+1) in
  help 0
  
(**porównywanie termów i formuł*)
let rec compare_term t1 t2=
  match(t1,t2) with
  |(F_Var(s1),F_Var(s2))->s1=s2
  |(B_Var(n1),B_Var(n2))->n1=n2
  |(Sym(sym1,xs),Sym(sym2,ys))->(sym1=sym2) && (equal compare_term xs ys)
  |_->false
let rec compare_form f1 f2= 
  match (f1,f2) with
  |(Leaf(t1),Leaf(t2))->compare_term t1 t2
  |(False,False)->true
  |(True,True)->true
  |(Rel(sym1,xs),Rel(sym2,ys))->(sym1=sym2) && (equal compare_term xs ys)
  |(Imp(f3,f4),Imp(f5,f6))->(compare_form f3 f5) && (compare_form f4 f6)
  |(And(f3,f4),And(f5,f6))->(compare_form f3 f5) && (compare_form f4 f6)
  |(Or(f3,f4),Or(f5,f6))->(compare_form f3 f5) && (compare_form f4 f6)
  |(Neg(f3),Neg(f4))->(compare_form f3 f4)
  |(All(s1,f3),All(s2,f4))->(compare_form f3 f4)
  |_->false 

(**Podstawienia za zmienne termów*) 
let rec substitute_in_term t_var t_sub term=
  match term with
  |B_Var(s1)->B_Var(s1)
  |F_Var(s1)->if t_var=s1 then t_sub else term
  |Sym(sym,xs)->Sym(sym,(List.map (fun x->substitute_in_term t_var t_sub x) xs))
let rec substitute_in_formula t_var t_sub form=
  match form with
  |Leaf(t)->Leaf(substitute_in_term t_var t_sub t)
  |False->False
  |True->True
  |Rel(sym,xs)->Rel(sym,(List.map (fun x->substitute_in_term t_var t_sub x) xs))
  |Imp(f1,f2)->Imp((substitute_in_formula t_var t_sub f1),(substitute_in_formula t_var t_sub f2))
  |And(f1,f2)->And((substitute_in_formula t_var t_sub f1),(substitute_in_formula t_var t_sub f2))
  |Or(f1,f2)->Or((substitute_in_formula t_var t_sub f1),(substitute_in_formula t_var t_sub f2)) 
  |Neg(f1)->Neg((substitute_in_formula t_var t_sub f1))
  |All(s1,f1)->if s1=t_var then All(s1,f1) else All(s1,(substitute_in_formula t_var t_sub f1))

(**substitute_with_d to pomocnicza formułą której używamy kiedy chcemy, żeby jakaś zmienna została związana przy podstawieniu, 
shift_up to pomocnicza funkcja która zwiększa wszystkie indeksy o 1*)
  let rec shift_up t=
  match t with
  |F_Var(s1)->F_Var(s1)
  |B_Var(n)->B_Var(n+1)
  |Sym(sym,xs)->Sym(sym,(List.map shift_up xs))

  let rec substitute_with_d_in_formula t_var t_sub form=
  match form with
  |Leaf(t)->Leaf(substitute_in_term t_var t_sub t)
  |False->False
  |True->True
  |Rel(sym,xs)->Rel(sym,(List.map (fun x->substitute_in_term t_var t_sub x) xs))
  |Imp(f1,f2)->Imp((substitute_in_formula t_var t_sub f1),(substitute_in_formula t_var t_sub f2))
  |And(f1,f2)->And((substitute_in_formula t_var t_sub f1),(substitute_in_formula t_var t_sub f2))
  |Or(f1,f2)->Or((substitute_in_formula t_var t_sub f1),(substitute_in_formula t_var t_sub f2)) 
  |Neg(f1)->Neg((substitute_in_formula t_var t_sub f1))
  |All(s1,f1)->if s1=t_var then All(s1,f1) else All(s1,(substitute_in_formula t_var (shift_up t_sub) f1))
  
(**sprawdzenie czy zmienna jest wolna *)
let rec free_variable_in_term t term=
  match term with
  |F_Var(s1)->t=s1
  |B_Var(s1)->false
  |Sym(s1,xs)->List.exists (fun x->free_variable_in_term t x) xs
                 
let rec free_variable_in_formula t form=
  match form with
  |Leaf(term)->free_variable_in_term t term
  |False->false
  |True->false
  |Rel(sym,xs)->List.exists (fun x->free_variable_in_term t x) xs
  |Imp(f1,f2)->free_variable_in_formula t f1 || free_variable_in_formula t f2
  |And(f1,f2)->free_variable_in_formula t f1 || free_variable_in_formula t f2
  |Or(f1,f2)->free_variable_in_formula t f1 || free_variable_in_formula t f2
  |Neg(f1)->free_variable_in_formula t f1
  |All(s1,f1)->free_variable_in_formula t f1 
(**zamiana formuł w postaci częściowych indeksów na postać kórej używa użytkownik*)
let rec de_de_brujin_term term var_map k=
  match term with
  |F_Var(s1)->Var_u(s1)
  |B_Var(n)->Var_u(Int_map.find (k-n) var_map)
  |Sym(s1,xs)->Sym_u(s1,List.map (fun x->de_de_brujin_term x var_map k) xs)
                 
let rec de_de_brujin_formula form var_map k=
  match form with 
  |Leaf(t)->Leaf_u(de_de_brujin_term t var_map k)
  |False->False_u
  |True->True_u
  |Rel(sym,xs)->Rel_u(sym,(List.map (fun x->de_de_brujin_term x var_map k) xs))
  |Imp(f1,f2)->Imp_u((de_de_brujin_formula f1 var_map k),(de_de_brujin_formula f2 var_map k))
  |And(f1,f2)->And_u((de_de_brujin_formula f1 var_map k),(de_de_brujin_formula f2 var_map k))
  |Or(f1,f2)->Or_u((de_de_brujin_formula f1 var_map k),(de_de_brujin_formula f2 var_map k))
  |Neg(f1)->Neg_u(de_de_brujin_formula f1 var_map k)
  |All(s1,f1)->(if free_variable_in_formula s1 f1 then 
                  let x=fresh_var (f1::(List.map (fun x->Leaf(F_Var(snd x))) (Int_map.bindings var_map))) 
                  in All_u(x,(de_de_brujin_formula f1 (Int_map.add k x var_map) (k+1)))
                else All_u(s1,(de_de_brujin_formula f1 (Int_map.add k s1 var_map) (k+1))))

let de_de_brujin f=
  de_de_brujin_formula f Int_map.empty 0


(**Bound variables to funkcja która przechodzi jeszcze raz formułę i związuje wszystkie niezwiązanne zmienne*)
let rec bv_term_help t map_var k=
  match t with
  |B_Var(n)->B_Var(n)
  |F_Var(str)->if is_numeric str then failwith "variable name cannot be numeric" else 
      if Var_map.mem str map_var then B_Var(k-(Var_map.find str map_var)) else F_Var(str)
  |Sym(str,xs)->Sym(str,(List.map (fun t->bv_term_help t map_var k) xs))

let bound_variables f= 
  let rec help f map_var k= 
    match f with
    |Leaf(t)->Leaf(bv_term_help t map_var k)
    |False->False 
    |True->True
    |Rel(s1,xs)->Rel(s1,(List.map (fun x->bv_term_help x map_var k) xs))
    |Imp(f1,f2)->Imp((help f1 map_var k),(help f2 map_var k))
    |And(f1,f2)->And((help f1 map_var k),(help f2 map_var k))
    |Or(f1,f2)->Or((help f1 map_var k),(help f2 map_var k))
    |Neg(f)->Neg(help f map_var k)
    |All(str,f)->All(str,(help f (Var_map.add str k map_var) (k+1))) in
  help f Var_map.empty 0
               
let rec btf_term_help t x k=
  match t with
  |B_Var(n)->if n=k then F_Var(x) else B_Var(n)
  |F_Var(str)->F_Var(str)
  |Sym(str,xs)->Sym(str,(List.map (fun t->btf_term_help t x k) xs))

(**Bounded to tree to formułą która działą dla formuł postaci Ax f. Usuwa ona ten kwantyfikator i zamienia wszystkie wystąpienia zmiennych
przez niego związanych na zmienne wolne *)
let bounded_to_free f= 
  let rec help f x k= 
    match f with
    |Leaf(t)->Leaf(btf_term_help t x k)
    |False->False 
    |True->True
    |Rel(s1,xs)->Rel(s1,(List.map (fun a->btf_term_help a x k) xs))
    |Imp(f1,f2)->Imp((help f1 x k),(help f2 x k))
    |And(f1,f2)->And((help f1 x k),(help f2 x k))
    |Or(f1,f2)->Or((help f1 x k),(help f2 x k))
    |Neg(f)->Neg(help f x k)
    |All(str,f)->if str=x then All(str,f) else All(str, help f x (k+1)) in
  match f with
  |All(x,f)->help f x 1
  |_->failwith "bounded_to_free-not All"