open Fol
open Fol_u

val de_brujin_term: term_u->term
val de_brujin: formula_u->formula
val equal: (term->term->bool)->term list->term list->bool
val fresh_var: formula list->string
val compare_form: formula->formula->bool
val compare_term: term->term->bool
val substitute_in_term: string->term->term->term
val substitute_in_formula: string->term->formula->formula
val free_variable_in_term: string->term->bool
val free_variable_in_formula: string->formula->bool
val de_de_brujin: formula->formula_u
val substitute_with_d_in_formula: string->term->formula->formula
val bound_variables: formula->formula
val bounded_to_free: formula->formula