open Eval;;
open Parse;;

let eq_proc exp =
  match (length exp),(car exp),(cadr exp) with
  | 2,(Atom (Int xx)),(Atom (Int yy)) -> make_bool (xx = yy)
  | _,x,y -> failwith (String.concat "" ["eq: type_error"; (string_of_object x);]);;

let plus_proc exp =
  match (length exp),(car exp),(cadr exp) with
  | 2,(Atom (Int xx)),(Atom (Int yy)) -> make_int (xx + yy)
  | _,x,y -> failwith (String.concat "" ["+: type_error"; (string_of_object x);]);;

let minus_proc exp =
  match (length exp),(car exp),(cadr exp) with
  | 2,(Atom (Int xx)),(Atom (Int yy)) -> make_int (xx - yy)
  | _,x,y -> failwith (String.concat "" ["-: type_error"; (string_of_object x);]);;

let times_proc exp =
  match (length exp),(car exp),(cadr exp) with
  | 2,(Atom (Int xx)),(Atom (Int yy)) -> make_int (xx * yy)
  | _,x,y -> failwith (String.concat "" ["*: type_error"; (string_of_object x);]);;

let env = make_init_env [((make_symbol "+"),(Prim_proc plus_proc));
                         ((make_symbol "-"),(Prim_proc minus_proc));
                         ((make_symbol "eq"),(Prim_proc eq_proc));
                         ((make_symbol "*"),(Prim_proc times_proc));];;

let rec repl env =
  let () = print_string "slp_lisp > "  in
  let () = flush stdout in
  let _ = eval (read_s_exp stdin) env |> string_of_object |> print_endline in
  repl env;;

repl env;;
