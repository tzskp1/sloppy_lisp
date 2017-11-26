type 'a proc = { args: 'a; body: 'a; env: ('a,'a) Hashtbl.t; prim: bool; func: ('a -> 'a) };;

type 'a dtype = string * 'a (* type_name,value *)

type atom = 
  | Int of int 
  | Float of float 
  | Str of string 
  | Bool of bool;;

type exp =
  | Nil
  | Atom of atom dtype
  | Symbol of string dtype
  | Cons of exp * exp
  | Prim_proc of (exp -> exp)
  | Proc of exp proc;;

type 'a tree =
  | Leaf of 'a
  | Node of ('a tree) list;;

let string_of_object ob =
  match ob with
  | Nil -> "Nil"
  | Symbol (_,x) -> (String.concat "" ["Symbol:"; x])
  | Cons (_,_)-> "Cons"
  | Proc _ -> "Proc"
  | Atom a ->
     match a with
     | (n,(Int v)) -> string_of_int v
     | (n,(Float v)) -> string_of_float v
     | (n,(Bool v)) -> string_of_bool v
     | (n,(Str v)) -> v;;

let int_of_atom value =
  match value with
  | Atom ("integer",(Int v)) -> v
  | _ -> failwith "not int";;

let make_int value = Atom ("integer",(Int value))

let make_float value = Atom ("float",(Float value))

let make_string value = Atom ("string",(Str value))

let make_bool value = Atom ("bool",(Bool value))

let make_symbol value = Symbol ("symbol",value)

let is_int s =
  try ignore (int_of_string s); true
  with _ -> false;;
 
let is_float s =
  try ignore (float_of_string s); true
  with _ -> false;;

let list_of_string str =
  let len = String.length str in
  let rec iter cnt = if cnt < len then str.[cnt] :: iter (cnt+1) else [] in 
  iter 0;;

let is_str str =
  let rec iter ls = 
    match ls with
    | '"' :: [] -> true 
    | '"' :: xs -> iter xs
    | _ -> false in iter (list_of_string str);;

let is_bool str =
  match str with
  | "true" | "false" -> true
  | _ -> false;;

let bool_val str =
  match str with
  | "true" -> true
  | "false" -> false
  | _ -> failwith "is not boolean";;

let rec separate_s_exp sexp =
  let rec classify str =
    match str with
    | [] -> ([],[])
    | (ch :: xs) ->
       match ch with
       | '(' -> (["("],xs)
       | ')' -> ([")"],xs)
       | ' ' -> ([],xs)
       | c ->
          match xs with
          | [] -> ((String.make 1 c) :: [],[])
          | ')' :: _ -> ((String.make 1 c) :: [],xs)
          | _ -> let (l,r) = classify xs in ((String.make 1 c) :: l,r) in
  match classify sexp with
  | ([],[]) -> []
  | ([],rem) -> separate_s_exp rem
  | (res,rem) -> String.concat "" res :: separate_s_exp rem;;

let rev ls =
  let rec iter ls res =
    match ls with
    | [] -> res
    | x :: xs -> iter xs (x :: res) in iter ls [];;

let str_tree_list_of_str_list sexp = 
  let rec s2exp sexp res =
    match (sexp,res) with
    | ([],_) -> res
    | (")" :: xs,y :: ys) -> (match ys with
                              | [] -> s2exp xs [[(Node (rev y))]]
                              | z :: zs -> s2exp xs (((Node (rev y)) :: z) :: zs))
    | ("(" :: x :: xs,_) -> s2exp xs ([Leaf x] :: res)
    | (n :: xs,y :: ys) -> s2exp xs (((Leaf n) :: y) :: ys)
    | (_,[]) -> failwith "paren_error" in rev (List.hd (s2exp sexp []));;
    (* | (_,[]) -> failwith "paren_error" in List.hd (List.hd (s2exp sexp []));; *)

let rec exp_of_str_tree str_tree =
  let classify str =
    if is_int str then make_int (int_of_string str)
    else if is_float str then make_float (float_of_string str)
    else if is_str str then make_string str
    else if is_bool str then make_bool (bool_val str)
    else make_symbol str in
  match str_tree with
  | Leaf x -> classify x
  | Node ls ->
     match ls with
     | [] -> failwith "empty_cons"
     | x :: [] -> (Cons ((exp_of_str_tree x),Nil))
     | x :: xs -> (Cons ((exp_of_str_tree x),exp_of_str_tree (Node xs)));;

let is_there_exp exp env = Hashtbl.mem env exp;;

let search_exp exp env = Hashtbl.find env exp;;

let bind exp value env = Hashtbl.add env exp value;;

let is_tagged_list tag exp =
  match (exp,tag) with
  | (Cons ((Symbol x),y),(Symbol t)) -> x = t
  | _ -> false;;

let is_quoted exp = is_tagged_list (make_symbol "quote") exp;;

let is_if exp = is_tagged_list (make_symbol "if") exp;;

let is_lambda exp = is_tagged_list (make_symbol "lambda") exp;;

let is_define exp = is_tagged_list (make_symbol "define") exp;;

let is_begin exp = is_tagged_list (make_symbol "begin") exp;;

let car exp =
  match exp with
  | Cons (x,y) -> x
  | _ -> failwith "is not list";;
  
let cdr exp =
  match exp with
  | Cons (x,y) -> y
  | _ -> failwith "is not list";;

let make_proc arg bod ev = { args=arg; body=bod; env=(Hashtbl.copy ev); prim=false; func=(fun _ -> Nil);};;

let make_prim_proc fn = { args=Nil; body=Nil; env=(Hashtbl.create 1); prim=true; func=fn;};;

let rec length exp =
  match exp with
  | Nil -> 0
  | Cons (x,y) -> 1 + length y
  | _ -> failwith "is not list";;

let plus_proc exp =
  match exp with
  | Cons (Atom ("integer",(Int x)),Cons (Atom ("integer",(Int y)),Nil)) -> make_int (x + y)
  | x -> failwith (String.concat "" ["+: type_error"; (string_of_object x);]);;

let minus_proc exp =
  match exp with
  | Cons (Atom ("integer",(Int x)),Cons (Atom ("integer",(Int y)),Nil)) -> make_int (x - y)
  | _ -> failwith "-: type_error";;

let times_proc exp =
  match exp with
  | Cons (Atom ("integer",(Int x)),Cons (Atom ("integer",(Int y)),Nil)) -> make_int (x * y)
  | _ -> failwith "*: type_error";;

let rec map f exp =
  match exp with
    | Nil -> Nil
    | Cons (x,y) -> Cons (f x,map f y)
    | _ -> failwith "is not list";;

let rec mapl f exp =
  match exp with
    | Cons (x,Nil) -> f x
    | Cons (x,y) -> let _ = f x in mapl f y
    | _ -> failwith "is not list";;

let rec zip xs ys =
  if (length xs = length ys) then 
    match (xs,ys) with
    | (Nil,_) -> Nil
    | (_,Nil) -> Nil
    | (Cons (x,y),Cons (z,w)) -> Cons (Cons(x,z),zip y w)
    | _ -> failwith "is not list"
  else failwith "argument length's error";;

let rec eval env exp =
  if is_quoted exp then (car (cdr exp))
  else if is_define exp then
    match car (cdr exp) with
    | Symbol x -> let () = (bind (car (cdr exp)) (eval env (car (cdr (cdr exp)))) env) in (make_string "OK")
    | _ -> failwith "is not symbol"
  else if is_lambda exp then Proc (make_proc (car (cdr exp)) (car (cdr (cdr exp))) env)
  else if is_begin exp then mapl (eval env) (cdr exp)
  else if is_if exp then
    match (eval env (car (cdr exp))) with
    | Atom ("bool",Bool true) ->  (eval env (car (cdr (cdr exp))))
    | Atom ("bool",Bool false) ->  (eval env (car (cdr (cdr (cdr exp)))))
    | _ -> failwith "is not boolean"
  else match exp with
       | Nil -> Nil
       | Atom _ -> exp
       | Cons (x,args) -> apply (eval env x) (map (eval env) args)
       | Symbol _ -> search_exp exp env
       | _ -> failwith "toriaezu"
and apply proc arg =
  match proc with
  | Proc pr ->
     (match pr with
     | {args=ags; body=bd; env=ev; prim=pm; func=fn;} -> 
        if not pm then
          let () = bind_sequence ags arg ev in (eval ev bd)
        else fn arg)
  | (Cons (_,_))-> failwith "cons"
  | Nil -> failwith "nil"
  | _ -> failwith "tori"
and bind_sequence args exp env =
  let bd (Cons (x,y)) = bind x y env in
  let _ = mapl bd (zip args exp) in ();;

let rec read_s_exp chan =
  try 
    let line = input_line chan in  
    String.concat "" [line; read_s_exp chan;]
  with
    e -> "";;

let rec loop () =
  let () = print_endline (read_line ()) in (loop ());;

let env = Hashtbl.create 10000;;
Hashtbl.add env (make_symbol "+") (Proc (make_prim_proc plus_proc));;
Hashtbl.add env (make_symbol "-") (Proc (make_prim_proc minus_proc));;
Hashtbl.add env (make_symbol "*") (Proc (make_prim_proc times_proc));;

List.map (fun x -> print_endline (string_of_object x))
  (List.map (fun x -> eval env (exp_of_str_tree x))
     (open_in "test.lisp" |> read_s_exp |> list_of_string |> separate_s_exp |> str_tree_list_of_str_list));;

List.map (fun x -> (exp_of_str_tree x))
  (open_in "test.lisp" |> read_s_exp |> list_of_string |> separate_s_exp |> str_tree_list_of_str_list);;
