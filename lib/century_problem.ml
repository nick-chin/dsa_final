(*******************************************)
(*       Part 1: Defining a Data Type      *)
(*******************************************)

type expr =
  | Add
  | Multi
  | Num of int;;


(* The 2 example solutions *)

let a = [Num (1); Num (2); Add; Num(3); Num (4); Add;
         Num (5); Multi; Num (6); Add; Num (7); Add;
         Num (8); Add; Num (9)];;

let b = [Num (1); Add; Num (2); Multi; Num (3); Add;
         Num (4); Add; Num (5); Add; Num (6); Num (7);
         Add; Num (8); Add; Num (9)];;



(* Dealing with multiple digits *)

let conjoin_num (ls : expr list) =
  let rec walk l acc_num acc_ls  =
    match l with
    | [] -> Num (acc_num) :: acc_ls
    | Num (x) :: t -> walk t (10 * acc_num + x) acc_ls
    | Add :: t -> walk t 0 (Add :: Num (acc_num) :: acc_ls)
    | Multi :: t -> walk t 0 (Multi :: Num (acc_num) :: acc_ls)
  in
  walk ls 0 [];;

conjoin_num a;;



(* Evaluating multiplication *)

let multi_num (ls : expr list) =
  let rec walk l acc =
    match l with
    | [] -> acc
    | Num (x) :: t -> walk t (Num (x) :: acc)
    | Add :: t -> walk t (Add :: acc)
    | Multi :: t ->
       let rol = List.tl t in
       let Num (x) = List.hd t in
       let Num (y) = List.hd acc in
       walk rol (Num (x * y) :: (List.tl acc))
  in
  walk ls [];;

multi_num @@ conjoin_num a;;



(* Evaluating addition *)

let add_num (ls : expr list) =
  let rec walk l acc =
    match l with
    | [] -> acc
    | Num (x) :: t -> walk t (acc + x)
    | Add :: t -> walk t acc
  in
  walk ls 0;;

add_num @@ multi_num @@ conjoin_num a;;
add_num @@ multi_num @@ conjoin_num b;;

(* All 3 in proper order *)

let eval_expr ls =
  add_num @@ multi_num @@ conjoin_num ls;;


(*******************************************)
(*         Part 2: Pretty Printing         *)
(*******************************************)

let pp (e : expr) =
  match e with
  | Num x -> Printf.printf "%d" x;
  | Add -> Printf.printf " + ";
  | Multi -> Printf.printf " * ";;

let print_expr (ls : expr list) =
  List.map pp ls;
  print_newline ();;

print_expr a;;
print_expr b;;

(*******************************************)
(*       Part 3: Generating Candidates     *)
(*******************************************)

(* Generate all 6561 candidates *)

let gen_candidates _ =
  let rec apply_expr lst n =
    match lst with
    | [] -> []
    | x -> [Num (n) :: Add :: x; Num (n) :: Multi :: x; Num (n) :: x]
  in

  let rec apply_num_and_expr big_list n =
    if n = 0 then big_list else
    match big_list with
    | [] -> apply_num_and_expr ([Num (n)] :: []) (n - 1)
    | x ->
       apply_num_and_expr (List.fold_left (fun i h -> (apply_expr h n) @ i) [] x) (n - 1)
  in
  apply_num_and_expr [] 9;;


(* Finding all solutions *)

let century_candidates = 
  List.filter (fun x -> eval_expr x = 100) (gen_candidates ());;
