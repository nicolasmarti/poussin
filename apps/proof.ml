open Printf
open Libpprinter
open Libparser
open Extlist
open Parser
open Pprinter
open Def
open Calculus_kernel

type goal = context * term;;

type tactics = goal list -> goal;;

module type Proofsystem =
   sig type thm
   end ;;

module Proven : Proofsystem =
  struct
    type thm = private term;;
  end;;

include Proven;;
