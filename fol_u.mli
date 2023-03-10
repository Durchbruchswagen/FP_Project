type term_u=
  |Var_u of string
  |Sym_u of string* term_u list 

type formula_u=
  |Leaf_u of term_u
  |False_u
  |True_u
  |Rel_u of string * term_u list
  |Imp_u of formula_u * formula_u
  |And_u of formula_u * formula_u
  |Or_u of formula_u * formula_u
  |Neg_u of formula_u
  |All_u of string * formula_u

