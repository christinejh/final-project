(*
                         CS 51 Final Project
                         MiniML -- Evaluation
                             Spring 2017
*)

(* This module implements a small untyped ML-like language under
   various operational semantics.
 *)

open Expr ;;

(* Exception for evaluator runtime, generated by a runtime error *)
exception EvalError of string ;;
(* Exception for evaluator runtime, generated by an explicit "raise" construct *)
exception EvalException ;;


(* Environments and values *)

module type Env_type = sig
    type env
    type value =
      | Val of expr
      | Closure of (expr * env)
    val create : unit -> env
    val close : expr -> env -> value
    val lookup : env -> varid -> value
    val extend : env -> varid -> value ref -> env
    val env_to_string : env -> string
    val value_to_string : ?printenvp:bool -> value -> string
  end

module Env : Env_type =
  struct
    type env = (varid * value ref) list
     and value =
       | Val of expr
       | Closure of (expr * env)

    (* Creates an empty environment *)
    let create () : env = [] ;;

    (* Creates a closure from an expression and the environment it's
       defined in *)
    let close (exp : expr) (env : env) : value =
      Closure (exp, env)

    (* Looks up the value of a variable in the environment *)
    let rec lookup (env : env) (varname : varid) : value =
      match env with
      | [] -> raise (EvalError ("Unbound variable " ^ varname))
      | (id, valref)::env_tail ->
          if id = varname then !valref
          else lookup env_tail varname

    (* Returns a new environment just like env except that it maps the
       variable varid to loc *)
    let rec extend (env : env) (varname : varid) (loc : value ref) : env =
      match env with
      | [] -> [(varname, loc)]
      | (id, valref)::tail ->
          if id = varname then (id, loc)::tail
          else (id, valref)::(extend tail varname loc)

    (* Returns a printable string representation of a value; the flag
       printenvp determines whether to include the environment in the
       string representation when called on a closure *)
    let rec value_to_string ?(printenvp : bool = true) (v : value) : string =
        match v with
        | Val exp -> exp_to_string exp
        | Closure (exp, env) ->
            if printenvp then (env_to_string env) ^ (exp_to_string exp)
            else exp_to_string exp

    (* Returns a printable string representation of an environment *)
    and env_to_string (env : env) : string =
      match env with
      | [] -> ""
      | (id, valref)::tail ->
          id ^ " = " ^ (value_to_string ~printenvp:false !valref) ^ "\n" ^ (env_to_string tail)

  end
;;

(* The evaluation function: Returns the result of type `value` of
   evaluating the expression `exp` in the environment `env`. In this
   initial implementation, we just convert the expression unchanged to
   a value and return it. *)


let eval_t exp _env = exp ;;

let eval_unop (op : unop) (value : expr) : expr =
  match op with
  | Negate ->
      match value with
      | Num x -> Num (-x)
      | _ -> raise (EvalError ("("^ (exp_to_string (Unop (op, value))) ^") bad redex"))

let eval_binop (op : binop) (valueL : expr) (valueR : expr) : expr =
  let extract_num (exp : expr) : int =
    match exp with
    | Num x -> x
    | _ -> raise (EvalError ("("^ (exp_to_string (Binop (op, valueL, valueR))) ^ ") bad redex"))
  in
  match op with
  | Plus -> Num ((extract_num valueL) + (extract_num valueR))
  | Minus -> Num ((extract_num valueL) - (extract_num valueR))
  | Times -> Num ((extract_num valueL) * (extract_num valueR))
  | Equals -> Bool ((extract_num valueL) = (extract_num valueR))
  | LessThan -> Bool ((extract_num valueL) < (extract_num valueR))


let rec eval_s (exp : expr) (env : Env.env) : expr =
  let extract_bool (e : expr) : bool =
    match e with
    | Bool b -> b
    | _ -> raise (EvalError ("("^ (exp_to_string exp) ^") bad redex"))
  in
  match exp with
  | Var id -> Var id
  | Num x -> Num x
  | Bool b -> Bool b
  | Unop (op, expr) -> eval_unop op (eval_s expr env)
  | Binop (op, exprL, exprR) -> eval_binop op (eval_s exprL env) (eval_s exprR env)
  | Conditional (cond, exprT, exprF) ->
      let c = eval_s cond env in
      if (extract_bool c) then eval_s exprT env
      else eval_s exprF env
  | Fun (id, expr) -> Fun (id, expr)
  | Let (id, expr, in_expr) ->
      let sub = subst id expr in_expr in
      eval_s sub env
  | Letrec (id, expr, in_expr) ->
      let sub_expr = subst id (Letrec (id, expr, Var id)) expr in
      let full_sub = subst id sub_expr in_expr in
      eval_s full_sub env
  | Raise -> raise EvalException
  | Unassigned -> Unassigned
  | App (f, arg) ->
      match eval_s f env with
      | Fun (id, expr) ->
          let sub = subst id arg expr in
          eval_s sub env
      | _ -> raise (EvalError ("("^ (exp_to_string (App (f,arg))) ^") bad redex"))

let rec eval_d (exp : expr) (env : Env.env) : expr =
  let extract_bool (e : expr) : bool =
    match e with
    | Bool b -> b
    | _ -> raise (EvalError ("("^ (exp_to_string exp) ^") bad redex"))
  in
  let extract_expr (value : Env.value) : expr =
    match value with
    | Env.Val expr -> expr
    | Env.Closure (expr, _) -> expr
  in
  match exp with
  | Var id -> eval_d (extract_expr (Env.lookup env id)) env
  | Num x -> Num x
  | Bool b -> Bool b
  | Unop (op, expr) -> eval_unop op (eval_d expr env)
  | Binop (op, exprL, exprR) -> eval_binop op (eval_d exprL env) (eval_d exprR env)
  | Conditional (cond, exprT, exprF) ->
      let c = eval_d cond env in
      if (extract_bool c) then eval_d exprT env
      else eval_d exprF env
  | Fun (id, expr) -> Fun (id, expr)
  | Let (id, expr, in_expr) ->
      let def_val = eval_d expr env in
      let new_env = Env.extend env id (ref (Env.close def_val env)) in
      eval_d in_expr new_env
  | Letrec (id, expr, in_expr) ->
      let id_value = ref (Env.Val Unassigned) in
      let new_env = Env.extend env id id_value in
      id_value := Env.close (eval_d expr new_env) env;
      eval_d in_expr new_env
  | Raise -> raise EvalException
  | Unassigned -> raise (EvalError "Attempt to evaluate unassigned variable")
  | App (f, arg) ->
      match eval_d f env with
      | Fun (id, expr) ->
          let arg_val = eval_d arg env in
          let new_env = Env.extend env id (ref (Env.close arg_val env)) in
          eval_d expr new_env
      | _ -> raise (EvalError ("("^ (exp_to_string (App (f,arg))) ^") bad redex"))

let eval_l _ = failwith "eval_l not implemented" ;;

(** The external evaluator, which can be either the identity function,
    the substitution model version or the dynamic or lexical
    environment model version. *)


let evaluate = eval_d ;;
