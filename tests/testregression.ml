open Printf
open Libpprinter
open Libparser

open Calculus_entry

let () = printf "calculus regression tests\n";;

let def = 
"
Inductive True : Prop
Constructor I: True

Inductive False : Prop
Inductive Not (P: Prop) : Prop
Constructor Contradiction  {P}: (P -> False) -> Not P

Inductive And (A B: Prop) : Prop
Constructor conj {A} {B}: A -> B -> And A B

Inductive Or (A B: Prop) : Prop
Constructor left {A} {B}: A -> Or A B
Constructor right {A} {B}: B -> Or A B

Inductive eq {A: Set} (a: A): A -> Prop
Constructor eq_refl {A} (a: A): eq a a

Inductive ReflexiveRel : Set
Constructor build_ReflexiveRel: (A: Set) -> (rel: A -> A -> Prop) -> (refl: (x: A) -> rel x x) -> ReflexiveRel

Definition ReflexiveRel_t {rel: ReflexiveRel} : Set :=  match rel with | build_ReflexiveRel A _ _ := A end

Definition ReflexiveRel_rel {rel: ReflexiveRel} : ReflexiveRel_t {rel} -> ReflexiveRel_t {rel} -> Prop := match rel with  | build_ReflexiveRel _ rel _ := rel end

Definition ReflexiveRel_refl {rel: ReflexiveRel} : (x: ReflexiveRel_t {rel}) -> ReflexiveRel_rel x x := match rel with  | build_ReflexiveRel _ _ refl := refl  end"

in 
process_string def;;
