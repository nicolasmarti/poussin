open Pycaml
open Printf
open Lang_intf

module PyLang =
  functor (L: Lang) -> struct

    (* defined terms *)
    let defined = ref []
    
    (* debug flag *)
    let debug = ref false;;

    (* the pyobject_registry: used for values of the language that can't be marshaled in python values (with its ref counter ) *)
    let pyobject_registry : (int, (L.value * int)) Hashtbl.t = Hashtbl.create 100;;

    (* just a debug function *)
    let show_pyobject_registry () =
      (* iter : ('a -> 'b -> unit) -> ('a, 'b) t -> unit *)
      Hashtbl.iter (fun id (te, rc) ->
	let s = L.value2string te in
	printf "%d: %s, %d\n" id s rc; flush Pervasives.stdout;    
      ) pyobject_registry;
      printf "\n\n"; flush Pervasives.stdout
    
    (* create the python module *)
    let mdl = pyimport_addmodule L.name;;
    let mdl_dict = pymodule_getdict mdl;;
    
    (* create the python class that will be used to store values *)
    let _ = python_exec (String.concat "" 
			   ["class Value"; L.name ;":
     # just register the id
     # the id should be already registered in ocaml
     def __init__(self, id):
         self.id=id

     # decref the term registered by id
     def __del__(self):
         try:
             ";L.name;".decref(self.id)
         except:
             return None

     # return the string representation
     def __str__(self):
         return ";L.name;".to_string(self.id)

     # application (here args is a tuple)
     def __call__(self, *args):
         return ";L.name;".apply(self.id, args)

     # size of the term (1 + number of explicite arguments)
     # def __len__(self):
     #    return ";L.name;".length(self.id)

def createValue";L.name;"(id):
    return Value";L.name;"(id)
"])

    (* grab the pyobjects *)
    let value_class = python_eval (String.concat "" ["Value"; L.name]);;
    let createValue_function = python_eval (String.concat "" ["createValue"; L.name]);;
    

    (* register a value, return the id *)
    let register_value (v: L.value) : int =  
      (* create a hash of the value *)
      let id = Hashtbl.hash v in
      if !debug then printf "id for %s --> %d\n" (L.value2string v) id;
      (* look if the value is already there *)
      if Hashtbl.mem pyobject_registry id then (
	(* yes: the same term is in here, just increment the counter *)
	if L.eq_value v (fst (Hashtbl.find pyobject_registry id)) then (
	  Hashtbl.replace pyobject_registry id (v, (snd (Hashtbl.find pyobject_registry id)) + 1);
	  id 
	)else (
	  (* yes: create a fresh id and add the value *)
	  let id = ref (Random.int 10000000) in
	  while Hashtbl.mem pyobject_registry !id do
	    id := Random.int 10000000
	  done;
	  let _ = Hashtbl.add pyobject_registry !id (v, 1) in
	  !id  
	)
      ) else   
	let _ = Hashtbl.add pyobject_registry id (v, 1) in
	id  

    (* the wrapping *)
    let wrap_value (v: L.value) =
      let id = register_value v in
      if !debug then printf "registered %s (%d)\n" (L.value2string v) id;
      let res = pycallable_asfun createValue_function [| pyint_fromint id |] in
      if !debug then printf "created Value for id %d\n" id;
      res
    ;;

    (* the unwrapping *)
    let unwrap_value value =
      let isValue = pyobject_isinstance (value, value_class) in
      if isValue = 1 then
	let id_object = pyobject_getattr (value, pystring_fromstring "id") in
	let id = pyint_asint id_object in
	if not (Hashtbl.mem pyobject_registry id) then
	  raise (Failure "unwrap_value: unknown id")
	else
	  let (v, _) = Hashtbl.find pyobject_registry id in
	  v        
      else
	raise (Failure "unwrap _value: not a value")
    
    (* the marshalling *)
    let marshal_value_python (v: L.value) =
      (* first let's try to marshall python value *)
      match L.marshal_to_python v with
	| Some o -> o
	| None -> wrap_value v
	  
    let marshal_python_value (o: pyobject) =
      (* first let's try to marshall python value *)
      match L.marshal_from_python o with
	| Some v -> v
	| None -> unwrap_value o

    (* now the function of the modul, called by the value object *)
    let _ = 
      python_interfaced_function 
	~register_as: (String.concat "" [L.name; ".apply"])
	~docstring:"application of a registered term with python arguments"
	[|IntType; TupleType|]
	(fun args ->
	  match args with
	    | [| id; args |] ->
	      let id = pyint_asint id in
	      if not (Hashtbl.mem pyobject_registry id) then (
		raise (Failure "_.apply: unknown id")
	      )
	      else (
		let args = pytuple_toarray args in
		let args = Array.map (fun arg -> marshal_python_value arg) args in
		try
		  let v = L.apply (fst (Hashtbl.find pyobject_registry id)) args in
		  let o = marshal_value_python v in
		  o
		with
		  | L.Exception err -> 
		    raise (Failure (L.error2string err))
		  | Failure s -> 
		    raise (Failure s)
		  | _ -> 
		    raise (Failure "_.apply: unknown exception")
	      )
		
	    | _ -> raise (Failure "_.apply: wrong arguments")
	)
    ;;

    let _ = 
      python_interfaced_function 
	~register_as: (String.concat "" [L.name; ".to_string"])
	~docstring:"returns string representation of a registered term"
	[|IntType|]
	(fun [| id |] ->
	  let id = pyint_asint id in
	  if not (Hashtbl.mem pyobject_registry id) then (
	    raise (Failure "_.to_string: unknown id")
	  )
	  else (
	    pystring_fromstring (L.value2string (fst (Hashtbl.find pyobject_registry id)))
	  )
	)
    ;;


    let _ = 
      python_interfaced_function 
	~register_as: (String.concat "" [L.name; ".decref"])
	~docstring:"decrement the ref. counter of a registered term"
	[|IntType|]
	(fun [| id |] ->
	  let id = pyint_asint id in
	  if not (Hashtbl.mem pyobject_registry id) then (
	    raise (Failure "_.decref: unknown id")
	  )
	  else (
	    let (value, refcounter) = Hashtbl.find pyobject_registry id in
	    let _ = if refcounter = 1 then
		Hashtbl.remove pyobject_registry id		    
	      else
		Hashtbl.replace pyobject_registry id (value, refcounter - 1) in
	    pynone ()
	  )
	)
    ;;

    let _ = 
      python_interfaced_function 
	~register_as: (String.concat "" [L.name; ".init"])
	~docstring:"initialize the context"
	[| |]
	(fun [| |] -> L.init (); pynone ())
    ;;
    
    let _ =
      python_interfaced_function 
      ~register_as: (String.concat "" [L.name; ".eval"])
      ~docstring:"enter a term"
      [|StringType|]
      (fun [| str |] ->
	let str = pystring_asstring str in
	try
	  let res = L.eval str in
	  marshal_value_python res	  
	with
	  | L.Exception err -> 
	    raise (Failure (L.error2string err))
      )
    ;;

    let _ =
      python_interfaced_function 
      ~register_as: (String.concat "" [L.name; ".definition"])
      ~docstring:"enter a definition"
      [|StringType|]
      (fun [| str |] ->
	let str = pystring_asstring str in
	try
	  let (consumed, defs) = L.definition str in
	  let names = Array.map (fun (hd1, hd2) ->
	    let pte = wrap_value hd2 in
	    let _ = pydict_setitemstring (mdl_dict, hd1, pte) in
	    hd1
	  ) defs in
	  defined := names::!defined;
	  pyint_fromint consumed	  
	with
	  | L.Exception err -> 
	    raise (Failure (L.error2string err))
      )
    ;;

    let _ =
      python_interfaced_function 
      ~register_as: (String.concat "" [L.name; ".undo_definition"])
      ~docstring:"undo previous definition"
      [| |]
      (fun [|  |] ->
	try
	  L.undo_definition (); 
	  let names = List.hd !defined in
	  defined := List.tl !defined;
	  Array.iter (fun hd -> ignore(pydict_delitemstring (mdl_dict, hd))) names;
	  pynone ()
	with
	  | L.Exception err -> 
	    raise (Failure (L.error2string err))
      )
    ;;
    
    (* finally import the module *)
    let _ = python_exec (String.concat "" ["import "; L.name]);;
    

end
