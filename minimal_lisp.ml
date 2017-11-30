type 'a proc = 'a * 'a * 'a list;;

type atom = 
  | Int of int 
  | Float of float 
  | Str of string 
  | Bool of bool;;

type exp =
  | Nil
  | Atom of atom
  | Symbol of string
  | Cons of (exp ref) * (exp ref)
  | Prim_proc of (exp -> exp)
  | Proc of exp proc;;

type 'a tree =
  | Leaf of 'a
  | Node of ('a tree) list;;

let car exp =
  match exp with
  | Cons (x,y) -> !x
  | _ -> failwith "is not list";;
  
let cdr exp =
  match exp with
  | Cons (x,y) -> !y
  | _ -> failwith "is not list";;

let set_car exp value = 
  match exp with
  | Cons (x,y) -> (x := value)
  | _ -> failwith "is not list";;

let set_cdr exp value = 
  match exp with
  | Cons (x,y) -> (y := value)
  | _ -> failwith "is not list";;

let cadr exp = car (cdr exp);;

let caddr exp = car (cdr (cdr exp));;

let cadddr exp = car (cdr (cdr (cdr exp)));;

let rec string_of_object ob =
  match ob with
  | Nil -> " Nil"
  | Symbol x -> String.concat "" [" Symbol:"; x]
  | Cons (x,y)-> String.concat "" [" Cons "; string_of_object !x; string_of_object !y]
  | Proc (a,b,c) -> String.concat "" [" Proc"; string_of_object a; string_of_object b;] (* string_of_env c;] *)
  | Prim_proc _ -> " Prim_proc"
  | Atom a ->
     match a with
     | Int v -> string_of_int v
     | Float v -> string_of_float v
     | Bool v -> string_of_bool v
     | Str v -> v;;

let string_of_env env =
  let ev_st (Cons (x,y)) = String.concat "\n" ["Symbols: "; string_of_object !x; "Values: "; string_of_object !y;] in
  String.concat "" (List.map ev_st env);;

let make_int value = Atom (Int value)

let make_float value = Atom (Float value)

let make_string value = Atom (Str value)

let make_bool value = Atom (Bool value)

let make_symbol value = Symbol value

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
  let left ls = 
    match ls with
    | '"' :: xs -> xs
    | _ -> [] in
  let rec right ls = 
    match ls with
    | [] -> false
    | '"' :: [] -> true 
    | _ :: xs -> right xs in right (left (list_of_string str));;

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
    | ([lf],[]) -> [Leaf lf] :: []
    | (_,[]) -> failwith "paren error" in rev (List.hd (s2exp sexp []));;

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
     | x :: [] -> (Cons (ref (exp_of_str_tree x),ref Nil))
     | x :: xs -> (Cons (ref (exp_of_str_tree x),ref (exp_of_str_tree (Node xs))));;

let search_frame exp frame =
  let rec iter xs ys =
    match xs,ys with
    | Nil,Nil -> raise Not_found
    | Cons (x,xs'),Cons (y,ys') -> if !x = exp then !y else iter !xs' !ys'
    | _ -> failwith "this pattern never occurs" in
  match frame with
  | Cons (xs,ys) -> iter !xs !ys
  | _ -> failwith "illformed frame";;

let rec add_frame symbol value frame =
  match frame with
  | Cons (xs,ys) -> let xs' = Cons (ref symbol,ref !xs) in
                    let ys' = Cons (ref value,ref !ys) in
                    let () = (xs := xs') in
                    let () = (ys := ys') in ()
  | _ -> failwith "illformed frame";;

let make_frame () = Cons (ref Nil,ref Nil);;

let make_env env = (make_frame ()) :: env;;

let rec search_exp exp env =
  match env with
  | [] -> raise Not_found
  | x :: xs ->
     try
       search_frame exp x
     with
       Not_found -> search_exp exp xs;;

let bind exp value env =
  match env with
  | [] -> failwith "environment is empty"
  | x :: _ -> add_frame exp value x;;

let is_tagged_list tag exp =
  match (exp,tag) with
  | (Cons (_,_),(Symbol t)) ->
     (match car exp with
     | Symbol x -> x = t
     | _ -> false)
  | _ -> false;;

let is_quoted exp = is_tagged_list (make_symbol "quote") exp;;

let is_if exp = is_tagged_list (make_symbol "if") exp;;

let is_lambda exp = is_tagged_list (make_symbol "lambda") exp;;

let is_define exp = is_tagged_list (make_symbol "define") exp;;

let is_begin exp = is_tagged_list (make_symbol "begin") exp;;

let rec length exp =
  match exp with
  | Nil -> 0
  | Cons (_,y) -> 1 + length !y
  | _ -> failwith "is not list";;

let rec map f exp =
  match exp with
    | Nil -> Nil
    | Cons (_,_) -> Cons (ref (f (car exp)),ref (map f (cdr exp)))
    | _ -> failwith "is not list";;

let rec zip xs ys =
  if (length xs = length ys) then 
    match (xs,ys) with
    | (Nil,_) -> Nil
    | (_,Nil) -> Nil
    | (Cons (x,y),Cons (z,w)) -> Cons (ref (Cons (x,z)),ref (zip !y !w))
    | _ -> failwith "is not list"
  else failwith "argument length's error";;

let rec foldr f exp init =
  match exp with
  | Nil -> init
  | Cons (x,y) -> f !x (foldr f !y init)
  | _ -> failwith "is not list";;

let rec foldl f exp init =
  let rec iter exp res =
    match exp with
    | Nil -> res
    | Cons (x,y) -> iter !y (f !x res)
    | _ -> failwith "is not list" in
  iter exp init;;

let rec eval exp env =
  let begin_impl exp env = foldl (fun x y -> eval x env) exp Nil in
  if is_quoted exp then cadr exp
  else if is_define exp then
    match cadr exp with
    | Symbol _ -> let () = bind (cadr exp) (eval (caddr exp) env) env in make_string "OK"
    | Cons (tag,args) ->
       (match !tag,!args with
        | Symbol _,Cons (_,_) -> let proc = Proc (!args,caddr exp,env) in
                                 let () = bind !tag proc env in make_string "OK"
        | _ -> failwith "illformed define")
    | _ -> failwith "illformed define"
  else if is_lambda exp then Proc (cadr exp,caddr exp,env)
  else if is_begin exp then begin_impl (cdr exp) env
  else if is_if exp then
    match eval (car (cdr exp)) env with
    | Atom (Bool true) ->  (eval (caddr exp) env)
    | Atom (Bool false) ->  (eval (cadddr exp) env)
    | _ -> failwith "is not boolean"
  else match exp with
       | Nil | Atom _ | Proc _ | Prim_proc _ -> exp
       | Cons (x,args) -> apply (eval !x env) (map (fun x -> eval x env) !args)
       | Symbol _ -> search_exp exp env
and apply proc args_val =
  let bind_sequence args exp env =
    let _ = map (fun (Cons (x1,x2)) -> let () = bind !x1 !x2 env in Nil) (zip args exp) in env in
  match proc with
  | Proc (args_sym,body,env) -> eval body (bind_sequence args_sym args_val (make_env env))
  | Prim_proc pr -> pr args_val
  | _ -> failwith (string_of_object proc);;

let make_init_env env =
  let rec iter frame env =
    match env with
    | [] -> ()
    | (x,y) :: xs -> let () = add_frame x y frame in
                     iter frame xs in
  let frame = make_frame () in
  let () = iter frame env in
  frame :: [];;

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

let filter_esc ls = List.map (fun x -> match x with
                                       | '\t' | '\n' -> ' '
                                       | _ -> x) ls;;

let rec read_s_exp chan =
  try 
    let line = input_line chan in  
    String.concat "" [line; read_s_exp chan;]
  with
    e -> "";;

let rec count_paren str_ls =
  match str_ls with
  | [] -> 0
  | '(' :: xs -> 1 + count_paren xs
  | ')' :: xs -> (-1) + count_paren xs
  | _ :: xs -> count_paren xs;;

let repl () =
  let env = make_init_env [((make_symbol "+"),(Prim_proc plus_proc));
                           ((make_symbol "-"),(Prim_proc minus_proc));
                           ((make_symbol "eq"),(Prim_proc eq_proc));
                           ((make_symbol "*"),(Prim_proc times_proc));] in
  let rec iter buf = 
    let total_buf = buf @ (read_line () |> list_of_string |> filter_esc) in
    if (count_paren total_buf) = 0
    then match total_buf |> separate_s_exp |> str_tree_list_of_str_list with
         | str_tree :: _ -> let res = eval (exp_of_str_tree str_tree) env in
                            let () = res |> string_of_object |> print_endline in
                            let () = "min_lisp > " |> print_string in
                            iter [] 
         | _ -> failwith "this pattern never occurs"
    else iter total_buf in
  let () = "min_lisp > " |> print_string in
  iter [];;

repl ();;
