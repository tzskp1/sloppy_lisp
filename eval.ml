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
  | Proc of exp * exp * exp list;;

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

let rec search_env exp env =
  match env with
  | [] -> raise Not_found
  | x :: xs ->
     try
       search_frame exp x
     with
       Not_found -> search_env exp xs;;

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
       | Symbol _ -> search_env exp env
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
