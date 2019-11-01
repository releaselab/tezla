open Batteries
open Michelscil

let sprint_list ?(first = "[") ?(last = "]") ?(sep = "; ") to_string l =
  let strout = BatIO.output_string () in
  List.print ~first ~last ~sep
    (fun outch x -> to_string x |> String.print outch)
    strout l ;
  BatIO.close_out strout

type pos = Unknown | Loc of int * int

type expr = Michelson_scil.expr

type ident = string

type decl = ident

type stmt = Michelson_scil.stmt

and _ node_data =
  | Stmt : stmt -> stmt node_data
  | Decl : decl -> decl node_data
  | Expr : expr -> expr node_data

and 'a t = {id: int; loc: pos; data: 'a node_data}

let counter = ref (-1)

let next_counter () =
  let () = counter := !counter + 1 in
  !counter

let create ?(loc = Unknown) data = {id= next_counter (); loc; data}

let get_node_data : type a. a t -> a =
 fun n -> match n.data with Stmt s -> s | Decl d -> d | Expr e -> e

let rec stmt_to_string =
  let open Printf in
  function
  | Cfg_var_decl v ->
      sprintf "var %s" (get_node_data v)
  | Cfg_assign (lv, rv) ->
      sprintf "%s = %s" (to_string lv) (to_string rv)
  | Cfg_guard e ->
      sprintf "test %s" (to_string e)
  | Cfg_jump ->
      sprintf "jump"
  | Cfg_call (f, args) ->
      sprintf "%s (%s)" (to_string f)
        (sprint_list ~first:"" ~last:"" ~sep:", " to_string args)

and to_string : type a. a t -> string =
 fun n ->
  match n.data with
  | Stmt _ ->
      stmt_to_string (get_node_data n)
  | Decl d ->
      d
  | Expr e ->
      Michelson_scil.expr_to_string e
