open Fol
open Fol_u
open Utility
type axiom =
| EqRefl (* ∀x.x = x *)
| EqElim of string * formula_u (* ∀y.∀z.y = z ⇒φ{x→y}⇒φ{x→z} *)
| PlusZ (* ∀n.0 + n = n *)
| PlusS (* ∀n.∀m.S(n) + m = S(n + m) *)
| Induction of string * formula_u
val axiom:axiom->formula
