(**definicja formuł na których operuje asystent.*)
type term=
  |F_Var of string
  |B_Var of int
  |Sym of string* term list 

type formula=
  |Leaf of term
  |False
  |True
  |Rel of string * term list
  |Imp of formula * formula
  |And of formula * formula
  |Or of formula * formula
  |Neg of formula
  |All of string * formula 