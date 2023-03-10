open Fol
open Fol_u
open Utility
type axiom =
| EqRefl (* ∀x.x = x *)
| EqElim of string * formula_u (* ∀y.∀z.y = z ⇒φ{x→y}⇒φ{x→z} *)
| PlusZ (* ∀n.0 + n = n *)
| PlusS (* ∀n.∀m.S(n) + m = S(n + m) *)
| Induction of string * formula_u

let axiom ax =
match ax with
| EqRefl ->
let x = fresh_var [] in
de_brujin (All_u(x, Rel_u("=", [Var_u(x); Var_u(x)])))
| EqElim(x, f) ->
let ff=de_brujin f in
let y = fresh_var [ff] in
let z = fresh_var [ff;Leaf(F_Var(y))] in
All(y, All(z, Imp(
Rel("=", [B_Var(2); B_Var(1)]),
Imp(
substitute_with_d_in_formula x (B_Var 2) ff,
substitute_with_d_in_formula x (B_Var 1) ff))))
| PlusZ ->
let n = fresh_var [] in
de_brujin (All_u(n, Rel_u("=",
[ Sym_u("+", [Sym_u("z", []); Var_u(n)])
; Var_u(n)
])))
| PlusS ->
let n = fresh_var [] in
let m = fresh_var [Leaf(F_Var(n))] in
de_brujin (All_u(n, All_u(m, Rel_u("=",
[ Sym_u("+", [Sym_u("s", [Var_u(n)]); Var_u(m)])
; Sym_u("s", [Sym_u("+", [Var_u(n); Var_u(m)])])
]))))
| Induction(x, f) ->
let ff=de_brujin f in
let n = fresh_var [ff] in
Imp(
substitute_in_formula x (Sym("z", [])) ff,
Imp(
All(n, Imp(
substitute_with_d_in_formula x (B_Var 1) ff,
substitute_with_d_in_formula x (Sym("s", [B_Var(1)])) ff)),
de_brujin (All_u(x,f))))
