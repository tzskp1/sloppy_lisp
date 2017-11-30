open Eval;;

type 'a tree =
  | Leaf of 'a
  | Node of ('a tree) list;;

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

let filter_esc ls = List.map (fun x -> match x with
                                       | '\t' | '\n' -> ' '
                                       | _ -> x) ls;;

let rec count_paren str_ls =
  match str_ls with
  | [] -> 0
  | '(' :: xs -> 1 + count_paren xs
  | ')' :: xs -> (-1) + count_paren xs
  | _ :: xs -> count_paren xs;;

let read_s_exp chan =
  let rec iter buf = 
    let total_buf = buf @ (input_line chan |> list_of_string |> filter_esc) in
    if (count_paren total_buf) = 0
    then exp_of_str_tree (total_buf |> separate_s_exp |> str_tree_list_of_str_list |> List.hd)
    else iter total_buf in iter [];;
