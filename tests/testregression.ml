open Printf
open Libpprinter

open Calculus_def
open Calculus_misc
open Calculus_substitution
open Calculus_substitution
open Calculus_engine
open Calculus_pprinter
open Calculus_parser

let () = printf "calculus regression tests\n";;


let te1 : term = lambda_ "x" (var_ (-1));;
printf "%s\n" (term2string [] te1);;

let te2 : term = forall_ "x" ~ty:(type_ (UName "")) (forall_ "x" ~ty:(var_ 0) (var_ 0));;
printf "%s\n" (term2string [] te2);;
