open Llvm;;
open Llvm_executionengine;;
open Llvm_target;;
open Llvm_scalar_opts;;

open Printf;;

let debug = ref false;;

(********************* general LLVM setup ********************)

ignore (initialize_native_target ());;

let optimize = ref false;;

let context = global_context ();;

let modul = create_module context "main";;

let engine = ExecutionEngine.create modul;;

let pass_manager = PassManager.create_function modul;;

let target_data = ExecutionEngine.target_data engine;;

(*printf "target_data := %s\n" (TargetData.as_string target_data);;*)

TargetData.add target_data pass_manager;;

(* optimizations *)

add_constant_propagation pass_manager;
add_sccp pass_manager;
add_dead_store_elimination pass_manager;
add_aggressive_dce pass_manager;
add_scalar_repl_aggregation pass_manager;
add_ind_var_simplification pass_manager;    
add_instruction_combination pass_manager;
add_licm pass_manager;
add_loop_unroll pass_manager;
add_loop_rotation pass_manager;
add_memory_to_register_promotion pass_manager;
(*add_memory_to_register_demotion pass_manager;*)
add_reassociation pass_manager;
add_jump_threading pass_manager;
add_cfg_simplification pass_manager;
add_tail_call_elimination pass_manager;
add_gvn pass_manager;
add_memcpy_opt pass_manager;
add_loop_deletion pass_manager;
add_lib_call_simplification pass_manager;

(* init passmanager *)
ignore (PassManager.initialize pass_manager);;

(******************* value encoding **********************)

(* some redefinition *)
let bool_type : lltype = i1_type context;;

let true_ : llvalue = const_int bool_type 1;;
let false_ : llvalue = const_int bool_type 0;;

let i8_type : lltype = i8_type context;;

let i32_type : lltype = i32_type context;;

let ptri8_type : lltype = pointer_type i8_type;;

let void_type : lltype = void_type context;;



(* utils *)

let log_i (x: int) (y: int) : int =
  let log_f = log (float x) /. log (float y) in
  let log_i = int_of_float log_f in
  if float log_i < log_f then log_i + 1 else log_i
;;

let div_i (x: int) (y: int) : int =
  let div_f = (float x) /. (float y) in
  let div_i = int_of_float div_f in
  if float div_i < div_f then div_i + 1 else div_i
;;

let rec power_i (x: int) (y: int) : int =
  if y = 0 then 1 else x * power_i x (y-1)
;;

let size_size_bits = Int64.to_int (size_in_bits target_data ptri8_type);;
let size_type : lltype = integer_type context size_size_bits;;

(* some usefull functions *)
let malloc_type : lltype = function_type ptri8_type [| size_type |];;
let malloc_ptr : llvalue = declare_function "malloc" malloc_type modul;;

let free_type : lltype = function_type void_type [| ptri8_type |];;
let free_ptr : llvalue = declare_function "free" free_type modul;;

let memalign_type : lltype = function_type ptri8_type [| size_type; size_type |];;
let memalign_ptr : llvalue = declare_function "memalign" memalign_type modul;;

let printi_type : lltype = function_type void_type [| size_type |];;
let printi_ptr : llvalue = declare_function "printi" printi_type modul;;

let printp_type : lltype = function_type void_type [| ptri8_type |];;
let printp_ptr : llvalue = declare_function "printp" printp_type modul;;

let memset_type : lltype = function_type ptri8_type [| ptri8_type; size_type; size_type |];;
let memset_ptr : llvalue = declare_function "memset" memset_type modul;;

let prints_type : lltype = function_type void_type [| ptri8_type |];;
let prints_ptr : llvalue = declare_function "prints" prints_type modul;;

(* gc functions *)
let gc_init_type : lltype = function_type i8_type [| size_type |];;
let gc_init_ptr : llvalue = declare_function "gc_init" gc_init_type modul;;

let gc_malloc_type : lltype = function_type ptri8_type [| size_type; i8_type |];;
let gc_malloc_ptr : llvalue = declare_function "gc_malloc" gc_malloc_type modul;;

let gc_free_type : lltype = function_type void_type [| ptri8_type |];;
let gc_free_ptr : llvalue = declare_function "gc_free" gc_free_type modul;;

let set_root_type : lltype = function_type void_type [| ptri8_type |];;
let set_root_ptr : llvalue = declare_function "set_root" set_root_type modul;;

let unset_root_type : lltype = function_type void_type [| ptri8_type |];;
let unset_root_ptr : llvalue = declare_function "unset_root" set_root_type modul;;

(**)

let llvm_printf str builder =
  let str = const_stringz context str in
  let alloca = build_alloca (type_of str) "alloca" builder in
  let _ = build_store str alloca builder in
  let alloca = build_bitcast alloca ptri8_type "alloca" builder in
  let _ = build_call prints_ptr [| alloca |] "" builder in
  ()
;;

let one = const_int (integer_type context size_size_bits) 1;;
let zero = const_int (integer_type context size_size_bits) 0;;
let two = const_int (integer_type context size_size_bits) 2;;
let three = const_int (integer_type context size_size_bits) 3;;
