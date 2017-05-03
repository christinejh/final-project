(*
       CS 51 Final Project
      MiniML -- Expressions
           Spring 2017
*)

open Expr ;;
open Miniml ;;
open Evaluation ;;

(* Stage 1 - exp_to_abstract_string *)

let expressions =
  [ "3";
    "2+3*4";
    "let f = fun x -> x in f 3";
    "let rec f = fun x -> if x = true then 2 else f x in f false"]
let abstracts =
  [ "Num(3)";
    "Binop(+, Num(2), Binop(*, Num(3), Num(4)))";
    "Let(f, Fun(x, Var(x)), App(Var(f), Num(3)))";
    "Letrec(f, Fun(x, Conditional(Binop(=, Var(x), True), Num(2), App(Var(f), Var(x)))), App(Var(f), False))"]
let rec check_abstracts (expr : string list) (abstract : string list) : unit =
  match (expr,abstract) with
  | (e::e_tail, a::a_tail) ->
      assert (exp_to_abstract_string (str_to_exp (e^";;")) = a);
      check_abstracts e_tail a_tail
  | _ -> ()

let _ = print_string "Checking abstract string creation...\n";
        check_abstracts expressions abstracts;
        print_string "OK\n"

(* Stage 2 - free_vars *)

let expressions =
  [ "fun y -> f (x + y)";
    "let x = 3 in let y = x in f x y";
    "let x = fun y -> x in x";
    "let rec x = fun y -> x in x";
    "x y z";
    "fun x -> 3 * (f y) + x"]
let sets =
  [ ["f";"x"];
    ["f"];
    ["x"];
    [];
    ["x";"y";"z"];
    ["f";"y"]]
let rec check_fv (expr : string list) (sets : string list list) : unit =
  match (expr, sets) with
  | (e::expr_tail, s::sets_tail) ->
      assert (same_vars (vars_of_list s) (free_vars (str_to_exp (e^";;"))));
      check_fv expr_tail sets_tail
  | _ -> ()

let _ = print_string "Checking free variables sets...\n";
        check_fv expressions sets;
        print_string "OK\n"

(* Stage 3 - substitutions *)

let expressions =
  [ "x + 3 * x";
    "fun y -> f (x + y)";
    "let x = 3 in let y = x in f x y";
    "let x = fun y -> x in x";
    "let rec x = fun y -> x in x";
    "let s = x + s in x + s";
    "let rec s = x + s in x + s"]
let subst_repl = Var "s"
let substituted =
  [ "s + 3 * s";
    "fun y -> f (s + y)";
    "let x = 3 in let y = x in f x y";
    "let x = fun y -> s in x";
    "let rec x = fun y -> x in x";
    "let var0 = s + s in s + var0";
    "let rec var1 = s + var1 in s + var1"]

let rec check_subst (exp : string list) (sub : string list) (repl : expr) : unit =
  match (exp, sub) with
  | (e::exp_tail, s::sub_tail) ->
      let expression = str_to_exp (e^";;") in
      let expectation = str_to_exp (s^";;") in
      assert ((subst "x" repl expression) = expectation);
      check_subst exp_tail sub_tail repl
  | _ -> ()

let _ = print_string "Checking substitutions...\n";
        check_subst expressions substituted subst_repl;
        print_string "OK\n"

(* Stage 4 - evaluation *)

let expressions =
  [ "4 + 2 * 3";
    "let x = 5 in (~x) + 1 * x";
    "if true then true else false";
    "let f = fun x -> x in f f 3";
    "let f = fun x -> 2*x in if f 1 < f 3 then f 10 else f 50";
    "let rec f = fun n -> if n < 5 then n else f (n-5) in f 28";
    "let rec f = fun n -> if n = 0 then 2 else f (n-1) * f (n-1) in f 4";
    "let rec f = fun n -> if n = 0 then 1 else if n = 1 then 1 else f (n-1) + f (n-2) in f 6";
    "let rec f = fun n -> if n = 0 then 1 else 2 * f (n-1) in f 5";
    "let rec f = fun n -> if n = 0 then 1 else n * f (n-1) in f 5"]
let values =
  [ "10";
    "0";
    "true";
    "3";
    "20";
    "3";
    "65536";
    "13";
    "32";
    "120"]

let rec check_eval (exp : string list) (values : string list) : unit =
  match (exp, values) with
  | (e::exp_tail, v::v_tail) ->
      let expr = (str_to_exp (e^";;")) in
      let expect = (str_to_exp (v^";;")) in
      assert ((eval_s expr (Env.create ())) = expect);
      check_eval exp_tail v_tail
  | _ -> ()

let _ = print_string "Checking evaluation...\n";
        check_eval expressions values;
        print_string "OK\n"

(* Stage 6 - environment *)

let expressions = [
  "5";
  "fun x -> x + x";
  "3";
  "let y = fun x -> x*x in y 2"]
let bindings = [
  "x";
  "y";
  "x";
  "y"]

let rec check_env (env : Env.env) (exp : string list) (bindings : string list) : unit =
  let extract_expr (v : Env.value) : expr =
    match v with
    | Env.Val exp -> exp
    | Env.Closure (exp, _) -> exp
  in
  match (exp, bindings) with
  | (e::e_tail, b::b_tail) ->
      let built_expr = str_to_exp (e^";;") in
      let new_env = Env.extend env b (ref (Env.Val built_expr)) in
      assert (extract_expr (Env.lookup new_env b) = built_expr);
      check_env new_env e_tail b_tail
  | _ -> ()

let env = ref (Env.create ())
let env_bindings = [
  ("x", "2+4");
  ("y", "fun x -> x*x");]

let rec apply_bindings (bindings : (string * string) list) : unit =
  match bindings with
  | (id, expr)::tail ->
      let v = Env.close (str_to_exp (expr^";;")) !env in
      env := Env.extend !env id (ref v);
      apply_bindings tail
  | _ -> ()

let _ = print_string "Checking environment...\n";
        apply_bindings env_bindings;
        assert (Env.env_to_string !env =
                "x = " ^ (exp_to_string (str_to_exp "2+4;;"))
                ^ "\ny = " ^ (exp_to_string (str_to_exp "fun x -> x*x;;")) ^ "\n");
        env := Env.extend !env "x" (ref (Env.Val (str_to_exp "0;;")));
        assert (Env.env_to_string !env =
                "x = " ^ (exp_to_string (str_to_exp "0;;"))
                ^ "\ny = "^ (exp_to_string (str_to_exp "fun x -> x*x;;")) ^ "\n")

let _ = check_env (Env.create ()) expressions bindings;
        print_string "OK\n"

(* Stage 7 - dynamically scoped environment evaluation *)

let expressions =
  [ "4 + 2 * 3";
    "let x = 5 in (~x) + 1 * x";
    "if true then true else false";
    "let f = fun x -> x in f f 3";
    "let f = fun x -> 2*x in if f 1 < f 3 then f 10 else f 50";
    "let rec f = fun n -> if n < 5 then n else f (n-5) in f 28";
    "let rec f = fun n -> if n = 0 then 2 else f (n-1) * f (n-1) in f 4";
    "let rec f = fun n -> if n = 0 then 1 else if n = 1 then 1 else f (n-1) + f (n-2) in f 6";
    "let rec f = fun n -> if n = 0 then 1 else 2 * f (n-1) in f 5";
    "let rec f = fun n -> if n = 0 then 1 else n * f (n-1) in f 5"]
let values =
  [ "10";
    "0";
    "true";
    "3";
    "20";
    "3";
    "65536";
    "13";
    "32";
    "120"]

let rec check_eval_d (exp : string list) (values : string list) : unit =
  match (exp, values) with
  | (e::exp_tail, v::v_tail) ->
      let expr = (str_to_exp (e^";;")) in
      let expect = (str_to_exp (v^";;")) in
      assert ((eval_d expr (Env.create ())) = expect);
      check_eval_d exp_tail v_tail
  | _ -> ()

let _ = print_string "Checking dynamically scoped environment evaluation...\n";
        check_eval expressions values

let raised = ref false
let _ =
  try
    let tmp = ref (str_to_exp "3;;") in
    tmp := eval_d (str_to_exp "let rec x = x in x;;") (Env.create ())
  with
    EvalError _ -> raised := true
let _ = assert !raised;
        print_string "OK\n"
