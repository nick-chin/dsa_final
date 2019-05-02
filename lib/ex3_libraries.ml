(* open Week_01 *)
(* let find_min ls = 
  let rec walk xs min = 
    match xs with
    | [] -> min
    | h :: t ->
      let min' = if h < min then h else min in
      walk t min'
  in match ls with
  | h :: t -> 
    let min = walk t h in
    Some min
  | _ -> None

let is_min ls m = 
  List.for_all (fun e -> e >= m) ls &&
  List.mem m ls
                  
let get_exn o = match o with
  | Some e -> e
  | _ -> raise (Failure "Empty option!")

let find_min_spec find_min_fun ls = 
  let result = find_min_fun ls in
  ls = [] && result = None ||
  is_min ls (get_exn result)

let generic_test_find_min find_min = 
  find_min_spec find_min [] &&
  find_min_spec find_min [1; 2; 3] &&
  find_min_spec find_min [31; 42; 239; 5; 100]

let test_find_min = 
  generic_test_find_min find_min

let find_min_walk_pre ls xs min = 
  is_min ls min ||
  List.exists (fun e -> e < min) xs

let find_min_walk_post ls _xs _min res = 
  is_min ls res

let find_min_with_invariant ls = 
  let rec walk xs min = 
    match xs with
    | [] -> 
      assert (find_min_walk_pre ls [] min);
      let res = min in
      assert (find_min_walk_post ls xs min res);
      res
    | h :: t ->
      let min' = if h < min then h else min in
      assert (find_min_walk_pre ls t min');
      let res = walk t min' in
      assert (find_min_walk_post ls xs min res);
      res
  in match ls with
  | h :: t -> 
    assert (find_min_walk_pre ls t h);
    let res = walk t h in
    assert (find_min_walk_post ls t h res);
    Some res
  | _ -> None

let is_min2 ls m1 m2 = 
  m1 < m2 &&
  List.for_all (fun e -> e == m1 || m2 <= e ) ls &&
  List.mem m2 ls
  

let find_min2_walk_inv ls xs m1 m2 = 
  is_min2 ls m1 m2 ||
  List.exists (fun e -> e < m1 || m1 <= e && e < m2 && e <> m1) xs

let find_min2 ls = 
  let rec walk xs m1 m2 = 
    match xs with
    | [] -> m2
    | h :: t ->
      let m1' = min h m1 in
      let m2' = if h < m1 then m1 else if h < m2 && h <> m1 then h else m2  in
      Printf.printf "m1' = %d, m2' = %d, Inv: %b\n" 
        m1' m2' (find_min2_walk_inv ls t m1' m2') ;
      assert (find_min2_walk_inv ls t m1' m2');
      walk t m1' m2'
  in match ls with
  | h1 :: h2 :: t ->
    let m1 = min h1 h2 in
    let m2 = max h1 h2 in
    Printf.printf "Inv_init: %b\n" (find_min2_walk_inv ls t m1 m2);
    assert (find_min2_walk_inv ls t m1 m2);
    let r = walk t m1 m2 in
    Some r
  | _ -> None

let find_min_loop ls =   
  let loop cur_tail cur_min = 
    while !cur_tail <> [] do
      let xs = !cur_tail in
      let h = List.hd xs in
      let min = !cur_min in
      cur_min := if h < min then h else min;
      cur_tail := List.tl xs
    done;
    !cur_min
  in match ls with
  | h :: t -> 
    let cur_tail = ref t in
    let cur_min = ref h in
    let min = loop cur_tail cur_min in
    Some min
  | _ -> None

let find_min_loop_inv ls = 
  let loop cur_tail cur_min = 
    assert (find_min_walk_pre ls !cur_tail !cur_min);
    while !cur_tail <> [] do
      let xs = !cur_tail in
      let h = List.hd xs in
      let min = !cur_min in
      cur_min := if h < min then h else min;
      cur_tail := List.tl xs;
      assert (find_min_walk_pre ls !cur_tail !cur_min);
    done;
    !cur_min
  in match ls with
  | h :: t -> 
    let cur_tail = ref t in
    let cur_min = ref h in
    assert (find_min_walk_pre ls !cur_tail !cur_min);
    let min = loop cur_tail cur_min in
    assert (find_min_walk_post ls !cur_tail !cur_min min);
    Some min
  | _ -> None

let insert_sort ls = 
  let rec walk xs acc =
    match xs with
    | [] -> acc
    | h :: t -> 
      let rec insert elem remaining = 
        match remaining with
        | [] -> [elem]
        | h :: t as l ->
          if h < elem 
          then h :: (insert elem t) else (elem :: l)
      in
      let acc' = insert h acc in
      walk t acc'
  in 
  walk ls []

let rec sorted ls = 
  match ls with 
  | [] -> true
  | h :: t -> 
    List.for_all (fun e -> e >= h) t && sorted t
    
let same_elems ls1 ls2 =
  List.for_all (fun e ->
      List.find_all (fun e' -> e = e') ls2 =
      List.find_all (fun e' -> e = e') ls1
    ) ls1 &&
  List.for_all (fun e ->
      List.find_all (fun e' -> e = e') ls2 =
      List.find_all (fun e' -> e = e') ls1
    ) ls2

let sorted_spec ls res = 
  same_elems ls res && sorted res
     
let sort_test sorter ls = 
  let res = sorter ls in
  sorted_spec ls res

(* Invariant for the outer loop *)
let insert_sort_walk_inv ls xs acc = 
  sorted acc &&
  same_elems (acc @ xs) ls
  
let insert_sort_insert_pre _elem prefix  =  sorted prefix

let insert_sort_insert_post res elem prefix  = 
  sorted res &&
  same_elems res (elem :: prefix)
  let insert_sort_with_inv ls = 
    let rec walk xs acc =
      match xs with
      | [] -> 
        let res = acc in
        (* walk's postcondition *)
        assert (sorted_spec ls res); 
        res
      | h :: t -> 
        let rec insert elem remaining = 
          match remaining with
          | [] -> 
            (* insert's postcondition *)
            assert (insert_sort_insert_post [elem] elem remaining);
            [elem]
          | h :: t as l ->
            if h < elem 
            then (
              (* insert's precondition *)
              assert (insert_sort_insert_pre elem t);
              let res = insert elem t in
              (* insert's postcondition *)
              (assert (insert_sort_insert_post (h :: res) elem remaining);
              h :: res))
            else 
              let res = elem :: l in
              (* insert's postcondition *)
              (assert (insert_sort_insert_post res elem remaining);
               res)
        in
        let acc' = (
           (* insert's precondition *)
           assert (insert_sort_insert_pre h acc);
           insert h acc) in
        (* walk's precondition *) 
        assert (insert_sort_walk_inv ls t acc');
        walk t acc'
    in 
    assert (insert_sort_walk_inv ls ls []);
    walk ls []                                  

let insert_inv prefix elem acc remaining run  = 
  sorted acc &&
  (if run
   then same_elems (acc @ elem :: remaining) (elem :: prefix)
   else same_elems acc (elem :: prefix))

let insert_sort_tail_walk_inv ls xs acc = 
  sorted acc &&
  same_elems (acc @ xs) ls

let insert_sort_tail ls = 
  let rec walk xs prefix =
    match xs with
    | [] -> prefix
    | h :: t -> 
        let rec insert elem acc remaining run = 
          if not run then acc
          else match remaining with
            | [] -> acc @ [elem]
            | h :: t as l ->
              if h < elem 
              then 
                let run' = true in
                let acc' = acc @ [h] in
                (* assert (insert_inv prefix elem acc' t run'); *)
                insert elem acc' t run'
              else 
                let run' = false in
                let acc' = acc @ (elem :: l) in
                (* assert (insert_inv prefix elem acc' t run'); *)
                insert elem acc' t run'
        in

        (* assert (insert_inv prefix h [] prefix true); *)
        let acc' = insert h [] prefix true in
        (* assert (insert_sort_tail_walk_inv ls t acc'); *)
        walk t acc'
  in 
  walk ls []

(* open Week_02 *)
let swap arr i j = 
  let tmp = arr.(i) in
  arr.(i) <- arr.(j);
  arr.(j) <- tmp

let print_int_sub_array l u arr =
  assert (l <= u);
  assert (u <= Array.length arr);
  Printf.printf "[| ";
  for i = l to u - 1 do
    Printf.printf "%d" arr.(i);
    if i < u - 1
    then Printf.printf "; "
    else ()      
  done;
  Printf.printf " |] "

let print_int_array arr = 
  let len = Array.length arr in
  print_int_sub_array 0 (len - 1) arr

let insert_sort arr = 
  let len = Array.length arr in
  for i = 0 to len - 1 do
    let j = ref i in 
    while !j > 0 && arr.(!j) < arr.(!j - 1) do
      swap arr !j (!j - 1);
      j := !j - 1
    done
  done

let insert_sort_backwards arr = 
  let len = Array.length arr in
  for i = len - 1 downto 0 do
    let j = ref i in 
    while !j < len - 1 && arr.(!j) > arr.(!j + 1) do
      swap arr !j (!j + 1);
      j := !j + 1
    done
  done

let rec sorted ls = 
  match ls with 
  | [] -> true
  | h :: t -> 
    List.for_all (fun e -> e >= h) t && sorted t

let array_to_list l u arr = 
  assert (l <= u);
  let res = ref [] in
  let i = ref (u - 1) in
  while l <= !i do
    res := arr.(!i) :: !res;
    i := !i - 1             
  done;
  !res
  
let sub_array_sorted l u arr = 
  let ls = array_to_list l u arr in 
  sorted ls

let array_sorted arr = 
  sub_array_sorted 0 (Array.length  arr) arr

let is_min ls min = 
  List.for_all (fun e -> min <= e) ls

let is_min_sub_array l u arr min = 
  let ls = array_to_list l u arr in 
  is_min ls min

let print_offset _ = 
  Printf.printf "  "

let insert_sort_print arr = 
  let len = Array.length arr in
  for i = 0 to len - 1 do
    print_int_sub_array 0 i arr; 
    print_int_sub_array i len arr;
    print_newline ();
    let j = ref i in 
    while !j > 0 && arr.(!j) < arr.(!j - 1) do
      print_offset ();
      print_int_sub_array 0 (i + 1) arr;
      print_int_sub_array (i + 1) len arr;
      print_newline ();
      swap arr !j (!j - 1);
      j := !j - 1;
    done;
    print_int_sub_array 0 (i + 1) arr; 
    print_int_sub_array (i + 1) len arr; 
    print_newline (); print_newline ()
  done

let insert_sort_inner_loop_inv j i arr = 
  is_min_sub_array !j i arr arr.(!j) &&
  sub_array_sorted 0 !j arr && 
  sub_array_sorted (!j + 1) (i + 1) arr

let insert_sort_outer_loop_inv i arr = 
  sub_array_sorted 0 i arr

let insert_sort_inv arr = 
  let len = Array.length arr in
  for i = 0 to len - 1 do
    assert (insert_sort_outer_loop_inv i arr);    
    let j = ref i in 
    while !j > 0 && arr.(!j) < arr.(!j - 1) do
      assert (insert_sort_inner_loop_inv j i arr);
      swap arr !j (!j - 1);
      j := !j - 1;
      assert (insert_sort_inner_loop_inv j i arr);
    done;
    assert (insert_sort_outer_loop_inv (i + 1) arr)
  done

let select_sort arr = 
  let len = Array.length arr in
  for i = 0 to len - 1 do
    for j = i to len - 1 do
      if arr.(j) < arr.(i)
      then swap arr i j
      else ()
    done
  done

let select_sort_print arr = 
  let len = Array.length arr in
  for i = 0 to len - 1 do
    print_int_sub_array 0 i arr; 
    print_int_sub_array i len arr;
    print_newline ();

    for j = i to len - 1 do
      print_offset ();
      Printf.printf "j = %d, a[j] = %d, a[i] = %d: " j arr.(j) arr.(i);
      print_int_sub_array 0 i arr;
      print_int_sub_array i len arr;
      print_newline ();

      if arr.(j) < arr.(i)
      then swap arr i j
      else ()
    done;

    print_int_sub_array 0 (i + 1) arr; 
    print_int_sub_array (i + 1) len arr;
    print_newline (); print_newline ();
  done

let suffix_larger_than_prefix i arr =
  let len = Array.length arr in
  let prefix = array_to_list 0 i arr in
  let suffix = array_to_list i len arr in
  List.for_all (fun e -> 
      List.for_all (fun f -> e <= f)  suffix
    ) prefix

let select_sort_outer_inv i arr =
  sub_array_sorted 0 i arr &&
  suffix_larger_than_prefix i arr

let select_sort_inner_inv j i arr = 
  is_min_sub_array i j arr arr.(i) &&
  sub_array_sorted 0 i arr &&
  suffix_larger_than_prefix i arr

let select_sort_inv arr = 
  let len = Array.length arr in
  for i = 0 to len - 1 do
    assert (select_sort_outer_inv i arr);
    for j = i to len - 1 do
      assert (select_sort_inner_inv j i arr);
      if arr.(j) < arr.(i)
      then swap arr i j
      else ();
      assert (select_sort_inner_inv (j + 1) i arr);
    done;
    assert (select_sort_outer_inv (i + 1) arr);
  done

let select_sort_general arr = 
  print_int_array arr; print_newline ();
  let len = Array.length arr in
  for i = 0 to len - 1 do
    Printf.printf "Sorted prefix: "; 
    print_int_array (Array.sub arr 0 i); print_newline ();
    (* Invariant: a[i] holds the minimun wrt a[i ... j] *)
    for j = i to len - 1 do
      if arr.(j) < arr.(i)
      then 
        (swap arr i j;
         print_int_array arr; print_newline ())        
      else ()
    done
  done

let sum_matrix m n = 
  let sum = ref 0 in
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
       sum := !sum + m.(i).(j)
    done
  done;
  !sum

let bubble_sort arr = 
  let len = Array.length arr in
  for i = 0 to len - 1 do
    print_int_sub_array 0 i arr; 
    print_int_sub_array i len arr;
    print_newline ();

    let j = ref (len - 1) in
    while !j > i do
      if arr.(!j) < arr.(!j - 1) 
      then swap arr !j (!j - 1)
      else ();
      j := !j - 1;
    done;

    print_int_sub_array 0 i arr; 
    print_int_sub_array i len arr;
    print_newline (); print_newline ();
  done

let bubble_sort_print arr = 
  let len = Array.length arr in
  for i = 0 to len - 1 do
    print_int_sub_array 0 i arr; 
    print_int_sub_array i len arr;
    print_newline ();

    let j = ref (len - 1) in
    while !j > i do
      print_offset ();
      print_int_sub_array 0 i arr; 
      print_int_sub_array i (!j) arr; 
      print_int_sub_array (!j) len arr;
      print_newline ();


      if arr.(!j) < arr.(!j - 1) 
      then swap arr !j (!j - 1)
      else ();
      j := !j - 1;
    done;

    print_int_sub_array 0 (i + 1) arr; 
    print_int_sub_array (i + 1) len arr;
    print_newline (); print_newline ();
  done

let bubble_sort_outer_inv i arr =
  sub_array_sorted 0 i arr

let bubble_sort_inner_inv i j arr =
  let len = Array.length arr in
  sub_array_sorted 0 i arr &&
  j >= i &&  
  is_min_sub_array j len arr arr.(j) &&
  suffix_larger_than_prefix i arr

let bubble_sort_inv arr = 
  let len = Array.length arr in
  (* Invariant: a[0 .. i] is sorted. *)  
  for i = 0 to len - 1 do
    assert (bubble_sort_outer_inv i arr);
    (* Invariant: a[j] is the smallest in a[j ... len - 1] *)
    for j = len - 1 downto i + 1 do
      assert (bubble_sort_inner_inv i j arr);
      if arr.(j) < arr.(j - 1) 
      then swap arr j (j - 1)
      else ();
      assert (bubble_sort_inner_inv i (j - 1) arr)
    done;
    assert (bubble_sort_outer_inv i arr);
  done

(* open Week_03 *)
let generate_keys bound len = 
  let acc = ref [] in
  for _i = 0 to len - 1 do
    acc := (Random.int bound) :: ! acc
  done;
  !acc

let generate_words length num =
  let random_ascii_char _ = 
    let rnd = (Random.int 26) + 97 in
    Char.chr rnd
  in
  let random_string _ = 
    let buf = Buffer.create length in
    for _i = 0 to length - 1 do
      Buffer.add_char buf (random_ascii_char ())
    done;
    Buffer.contents buf
  in
  let acc = ref [] in
  for _i = 0 to num - 1 do
    acc := (random_string ()) :: ! acc
  done;
  !acc

let iota n = 
  let rec walk acc m = 
    if m < 0 
    then acc
    else walk (m :: acc) (m - 1)
  in
  walk [] n

let list_zip ls1 ls2 = 
  let rec walk xs1 xs2 k = match xs1, xs2 with
    | h1 :: t1, h2 :: t2 -> 
      walk t1 t2 (fun acc -> k ((h1, h2) :: acc))
    | _ -> k []
  in
  walk ls1 ls2 (fun x -> x) 

let generate_key_value_array len = 
  let kvs = list_zip (generate_keys len len) (generate_words 5 len) in
  let almost_array = list_zip (iota (len - 1)) kvs in
  let arr = Array.make len (0, "") in
  List.iter (fun (i, kv) -> arr.(i) <- kv) almost_array;
  arr

let time f x =
  let t = Sys.time () in
  let fx = f x in
  Printf.printf "Execution elapsed time: %f sec\n"
    (Sys.time () -. t);
  fx

let new_insert_sort arr = 
  let len = Array.length arr in
  for i = 0 to len - 1 do
    let j = ref i in
    while !j > 0 && (fst arr.(!j - 1)) > (fst arr.(!j)) do
      swap arr !j (!j - 1);
      j := !j - 1
    done
  done

let linear_search arr k = 
  let len = Array.length arr in
  let res = ref None in
  let i = ref 0 in 
  while !i < len && !res = None do
    (if fst arr.(!i) = k 
    then res := Some ((!i, arr.(!i))));
    i := !i + 1
  done;
  !res

let binary_search arr k = 
  let rec rank lo hi = 
    if hi <= lo 
    then 
      (* Empty array *)
      None
    (* Converged on a single element *)
    else 
      let mid = lo + (hi - lo) / 2 in
      if fst arr.(mid) = k 
      then Some (arr.(mid))
      else if fst arr.(mid) < k
      then rank (mid + 1) hi 
      else rank lo mid  
  in
  rank 0 (Array.length arr)

let binary_search_print arr k = 
  let rec rank lo hi = 
    Printf.printf "Subarray: [";
    let ls = array_to_list lo hi arr in
    List.iter (fun (k, v) -> Printf.printf "(%d, %s); " k v) ls;
    Printf.printf "]\n\n";
    if hi <= lo 
    then 
      (* Empty array *)
      None
    (* Converged on a single element *)
    else 
      let mid = lo + (hi - lo) / 2 in
      if fst arr.(mid) = k 
      then Some (arr.(mid))
      else if fst arr.(mid) < k
      then rank (mid + 1) hi 
      else rank lo mid  
  in
  rank 0 (Array.length arr)

let binary_search_rank_pre arr lo hi k = 
  let len = Array.length arr in 
  let ls = array_to_list 0 len arr in
  let ls' = array_to_list lo hi arr in
  if List.exists (fun e -> fst e = k) ls
  then List.exists (fun e -> fst e = k) ls'
  else not (List.exists (fun e -> fst e = k) ls')

let binary_search_inv arr k = 
  let rec rank lo hi = 
    Printf.printf "lo = %d, hi = %d\n" lo hi;
    Printf.printf "Subarray: [";
    let ls = array_to_list lo hi arr in
    List.iter (fun (k, v) -> Printf.printf "(%d, %s); " k v) ls;
    Printf.printf "]\n";
    if hi <= lo 
    then 
      (* Empty array *)
      None
    (* Converged on a single element *)
    else 
      let mid = lo + (hi - lo) / 2 in
      Printf.printf "mid = %d\n" mid;
      if fst arr.(mid) = k 
      then Some (arr.(mid))
      else if fst arr.(mid) < k
      then
        (Printf.printf "THEN: lo = %d, hi = %d\n\n" (mid + 1) hi;
        assert (binary_search_rank_pre arr (mid + 1) hi k);
        rank (mid + 1) hi) 
      else 
        (Printf.printf "ELSE: lo = %d, hi = %d\n\n" lo mid;
        assert (binary_search_rank_pre arr lo mid k);
         rank lo mid)
  in
  let len = Array.length arr in 
  assert (binary_search_rank_pre arr 0 len k);
  rank 0 len
    
let rec rank arr k lo hi = 
  if hi <= lo 
  then 
    (* Empty array *)
    None
    (* Converged on a single element *)
  else 
    let mid = lo + (hi - lo) / 2 in
    if fst arr.(mid) = k 
    then Some (arr.(mid))
    else if fst arr.(mid) < k
    then rank arr k (mid + 1) hi 
    else rank arr k lo mid
        
let exponential_search arr k = 
  let len = Array.length arr in
  let rec inflate bound = 
    Printf.printf "Bound = %d\n" bound;
    if bound < len && fst arr.(bound) < k 
    then inflate (bound * 2)
    else if bound < len then bound else len
  in
  if len = 0 then None
  else
    let bound = inflate 1 in
    rank arr k 0 bound

let merge from1 from2 dest lo hi =
  let len1 = Array.length from1 in 
  let len2 = Array.length from2 in 
  let i = ref 0 in
  let j = ref 0 in
  for k = lo to hi - 1 do
    if !i >= len1 
    then (dest.(k) <- from2.(!j); j := !j + 1)
    else if !j >= len2
    then (dest.(k) <- from1.(!i); i := !i + 1)
    else if fst from1.(!i) <= fst from2.(!j)
    then (dest.(k) <- from1.(!i); i := !i + 1)
    else (dest.(k) <- from2.(!j); j := !j + 1)
  done

let copy_array arr lo hi =
  let len = hi - lo in
  assert (len >= 0);
  if len = 0 then [||]
  else 
    let res = Array.make len arr.(lo) in
    for i = 0 to len - 1 do
      res.(i) <- arr.(i + lo)
    done;
    res
    
let merge_sort arr = 
  let rec sort a = 
    let lo = 0 in
    let hi = Array.length a in
    if hi - lo <= 1 then ()
    else
      let mid = lo + (hi - lo) / 2 in
      let from1 = copy_array a lo mid in
      let from2 = copy_array a mid hi in
      sort from1; sort from2;
      merge from1 from2 a lo hi
  in
  sort arr

let rec sorted ls = 
  match ls with 
  | [] -> true
  | h :: t -> 
    List.for_all (fun e -> fst e >= fst h) t && sorted t

let array_to_list l u arr = 
  assert (l <= u);
  let res = ref [] in
  let i = ref (u - 1) in
  while l <= !i do
    res := arr.(!i) :: !res;
    i := !i - 1             
  done;
  !res
  
let sub_array_sorted l u arr = 
  let ls = array_to_list l u arr in 
  sorted ls

let array_sorted arr = 
  sub_array_sorted 0 (Array.length  arr) arr

let merge_pre from1 from2 = 
  array_sorted from1 && array_sorted from2

let same_elems ls1 ls2 =
  List.for_all (fun e ->
      List.find_all (fun e' -> e = e') ls2 =
      List.find_all (fun e' -> e = e') ls1
    ) ls1 &&
  List.for_all (fun e ->
      List.find_all (fun e' -> e = e') ls2 =
      List.find_all (fun e' -> e = e') ls1
    ) ls2

let merge_post from1 from2 arr lo hi = 
  array_sorted arr &&
  (let l1 = array_to_list 0 (Array.length from1) from1 in
  let l2 = array_to_list 0 (Array.length from2) from2 in
  let l = array_to_list lo hi arr in
  same_elems (l1 @ l2) l)
  
let merge_sort_inv arr = 
  let rec sort a = 
    let hi = Array.length a in
    let lo = 0 in
    if hi - lo <= 1 then ()
    else
      let mid = lo + (hi - lo) / 2 in
      let from1 = copy_array a lo mid in
      let from2 = copy_array a mid hi in
      sort from1; sort from2;
      assert (merge_pre from1 from2);
      merge from1 from2 a lo hi;
      assert (merge_post from1 from2 a lo hi)
  in
  sort arr

(* open Week_06 *)
module type AbstractStack = sig
  type 'e t
  val mk_stack : int -> 'e t
  val is_empty : 'e t -> bool
  val push : 'e t -> 'e -> unit
  val pop : 'e t -> 'e option
end

module ListBasedStack : AbstractStack = struct
  type 'e t = 'e list ref
  let mk_stack _ = ref []
  let is_empty s = match !s with
    | [] -> true
    | _ -> false
  let push s e = 
    let c = !s in
    s := e :: c
  let pop s = match !s with
    | h :: t ->
      s := t; Some h
    | _ -> None
end

module ArrayBasedStack : AbstractStack = struct
  type 'e t = {
    elems   : 'e option array;
    cur_pos : int ref 
  }
  let mk_stack n = {
    elems = Array.make n None;
    cur_pos = ref 0
  }
  let is_empty s = !(s.cur_pos) = 0
  let push s e = 
    let pos = !(s.cur_pos) in 
    if pos >= Array.length s.elems 
    then raise (Failure "Stack is full")
    else (s.elems.(pos) <- Some e;
          s.cur_pos := pos + 1)
  let pop s = 
    let pos = !(s.cur_pos) in
    let elems = s.elems in
    if pos <= 0 then None
    else (
      let res = elems.(pos - 1) in
      s.elems.(pos - 1) <- None;
      s.cur_pos := pos - 1;
      res)
end

module type Queue = 
sig
  type 'e t
  val mk_queue : int -> 'e t
  val is_empty : 'e t -> bool
  val is_full : 'e t -> bool
  val enqueue : 'e t -> 'e -> unit
  val dequeue : 'e t -> 'e option
  val queue_to_list : 'e t -> 'e list
end

module QueuePrinter(Q: Queue) = struct

let print_queue q pp = 
  Printf.printf "[";
  List.iter (fun e ->
    Printf.printf "%s; " (pp e))
    (Q.queue_to_list q);
  Printf.printf "]\n"
end

module DoublyLinkedList = 
struct
  type 'e dll_node = {
    value : 'e ref;
    prev  : 'e dll_node option ref;
    next  : 'e dll_node option ref
  }
  type 'e t = 'e dll_node option

  let mk_node e = {
    value = ref e;
    prev = ref None;
    next = ref None
  }

  let prev n =  !(n.prev)
  let next n =  !(n.next)
  let value n = !(n.value)
  let set_value n v = n.value := v

  let insert_after n1 n2 = 
    let n3 = next n1 in
    (match n3 with 
     | Some n -> n.prev := Some n2
     | _ -> ());
    n2.next := n3;
    n1.next := Some n2;
    n2.prev := Some n1

  let insert_before n1 n2 = 
    let n0 = prev n2 in
    (match n0 with 
     | Some n -> n.next := Some n1
     | _ -> ());
    n1.prev := n0;
    n1.next := Some n2;
    n2.prev := Some n1

  let rec move_to_head n = 
    match prev n with
    | None -> None
    | Some m -> move_to_head m
    
  let to_list_from n = 
    let res = ref [] in
    let iter = ref (Some n) in
    while !iter <> None do
      let node = (get_exn !iter) in
      res := (value node) :: ! res;
      iter := next node  
    done;
    List.rev !res

  let remove n = 
    (match prev n with
    | None -> ()
    | Some p -> p.next := next n);
    (match next n with
    | None -> ()
    | Some nxt -> nxt.prev := prev n);
end

module DLLBasedQueue : Queue = struct
open DoublyLinkedList

  type 'e t = {
    head : 'e dll_node option ref;
    tail : 'e dll_node option ref;
  }

  let mk_queue _sz = 
    {head = ref None; 
     tail = ref None}
  
  let is_empty q = 
    !(q.head) = None
    
  let is_full _q = false
    
  let enqueue q e = 
    let n = mk_node e in
    (* Set the head *)
    (if !(q.head) = None
     then q.head := Some n);
    (* Extend the tail *)
    (match !(q.tail) with
     | Some t -> insert_after t n;
     | None -> ());
    q.tail := Some n 

  let dequeue q =
    match !(q.head) with
    | None -> None
    | Some n -> 
      let nxt = next n in
      q.head := nxt;
      remove n; (* This is not necessary *)
      Some (value n)

  let queue_to_list q = match !(q.head) with
    | None -> []
    | Some n -> to_list_from n

end

module DLQPrinter = QueuePrinter(DLLBasedQueue)

let pp (k, v) = Printf.sprintf "(%d, %s)" k v

let print_queue q = DLQPrinter.print_queue q pp

module type Hashable = sig
type t
val hash : t -> int
end

module type HashTable = functor 
(H : Hashable) -> sig
type key = H.t
type 'v hash_table
val mk_new_table : int -> 'v hash_table 
val insert : (key * 'v) hash_table -> key -> 'v -> unit
val get : (key * 'v) hash_table -> key -> 'v option
val remove : (key * 'v) hash_table -> key -> unit
end
  
module ListBasedHashTable : HashTable = functor (H : Hashable) -> struct
type key = H.t

type 'v hash_table = {
  buckets : 'v list array;
  size : int 
}

let mk_new_table size = 
  let buckets = Array.make size [] in
  {buckets = buckets;
   size = size}

let insert ht k v = 
  let hs = H.hash k in
  let bnum = hs mod ht.size in 
  let bucket = ht.buckets.(bnum) in
  let clean_bucket = 
    List.filter (fun (k', _) -> k' <> k) bucket in
  ht.buckets.(bnum) <- (k, v) :: clean_bucket

let get ht k = 
  let hs = H.hash k in
  let bnum = hs mod ht.size in 
  let bucket = ht.buckets.(bnum) in
  let res = List.find_opt (fun (k', _) -> k' = k) bucket in
  match res with 
  | Some (_, v) -> Some v
  | _ -> None

(* Slow remove - introduce for completeness *)
let remove ht k = 
  let hs = H.hash k in
  let bnum = hs mod ht.size in 
  let bucket = ht.buckets.(bnum) in
  let clean_bucket = 
    List.filter (fun (k', _) -> k' <> k) bucket in
  ht.buckets.(bnum) <- clean_bucket
end

module HashTableIntKey = ListBasedHashTable 
  (struct type t = int let hash i = i end)

(* open Week_08_HashTable;; *)
module type HashTable = sig
  type key
  type 'v hash_table
  val mk_new_table : int -> (key * 'v) hash_table 
  val insert : (key * 'v) hash_table -> key -> 'v -> unit
  val get : (key * 'v) hash_table -> key -> 'v option
  val remove : (key * 'v) hash_table -> key -> unit
  val print_hash_table : 
    (key -> string) ->
    ('v -> string) ->
    (key * 'v) hash_table -> unit
end;;

module HashTableTester(H : HashTable) = struct

  module MyHT = H
  open MyHT

  let mk_test_table_from_array_length a m = 
    let n = Array.length a in
    let ht = mk_new_table m in
    for i = 0 to n - 1 do
      insert ht a.(i) a.(i)
    done;
    ht

  let test_table_get ht a = 
    let len = Array.length a in
    for i = 0 to len - 1 do
      let e = get ht a.(i) in
      assert (e <> None);
      (* let x = Week_01.get_exn e in *)
      let x = get_exn e in
      assert (x = a.(i))
    done;
    true
end;;

module type KeyType = sig
  type t
end;;

module SimpleListBasedHashTable(K: KeyType) = struct
  type key = K.t

  type 'v hash_table = {
    buckets : 'v list array;
    capacity : int; 
  }

  let mk_new_table cap = 
    let buckets = Array.make cap [] in
    {buckets = buckets;
     capacity = cap}
  
  let insert ht k v = 
    let hs = Hashtbl.hash k in
    let bnum = hs mod ht.capacity in 
    let bucket = ht.buckets.(bnum) in
    let clean_bucket = 
      List.filter (fun (k', _) -> k' <> k) bucket in
    ht.buckets.(bnum) <- (k, v) :: clean_bucket

  let get ht k = 
    let hs = Hashtbl.hash k in
    let bnum = hs mod ht.capacity in 
    let bucket = ht.buckets.(bnum) in
    let res = List.find_opt (fun (k', _) -> k' = k) bucket in
    match res with 
    | Some (_, v) -> Some v
    | _ -> None

  (* Slow remove - introduce for completeness *)
  let remove ht k = 
    let hs = Hashtbl.hash k in
    let bnum = hs mod ht.capacity in 
    let bucket = ht.buckets.(bnum) in
    let clean_bucket = 
      List.filter (fun (k', _) -> k' <> k) bucket in
    ht.buckets.(bnum) <- clean_bucket

  let print_hash_table ppk ppv ht = 
    let open Printf in
    print_endline @@ sprintf "Capacity: %d" (ht.capacity);
    print_endline "Buckets:";
    let buckets = (ht.buckets) in
    for i = 0 to (ht.capacity) - 1 do
      let bucket = buckets.(i) in
      if bucket <> [] then (
        (* Print bucket *)
        let s = List.fold_left 
            (fun acc (k, v) -> acc ^ (sprintf "(%s, %s); ") (ppk k) (ppv v)) "" bucket in
        printf "%d -> [ %s]\n" i s)
    done
end;;

module IntString = struct type t = int * string end;;
module SHT = SimpleListBasedHashTable(IntString);;
module SimpleHTTester = HashTableTester(SHT);;

let pp_kv (k, v) = Printf.sprintf "(%d, %s)" k v;;

module ResizableListBasedHashTable(K : KeyType) = struct
  type key = K.t

  type 'v hash_table = {
    buckets : 'v list array ref;
    size : int ref; 
    capacity : int ref; 
  }

  let mk_new_table cap = 
    let buckets = Array.make cap [] in
    {buckets = ref buckets;
     capacity = ref cap;
     size = ref 0}

  let rec insert ht k v = 
    let hs = Hashtbl.hash k in
    let bnum = hs mod !(ht.capacity) in 
    let bucket = !(ht.buckets).(bnum) in
    let clean_bucket = 
      List.filter (fun (k', _) -> k' <> k) bucket in
    let new_bucket = (k, v) :: clean_bucket in
    !(ht.buckets).(bnum) <- new_bucket;
    (* Increase size *)
    (if List.length bucket < List.length new_bucket
    then ht.size := !(ht.size) + 1);
    (* Resize *)
    if !(ht.size) > !(ht.capacity) + 1
    then resize_and_copy ht

  and resize_and_copy ht =
    let new_capacity = !(ht.capacity) * 2 in
    let new_buckets = Array.make new_capacity [] in
    let new_ht = {
      buckets = ref new_buckets;
      capacity = ref new_capacity;
      size = ref 0;
    } in
    let old_buckets = !(ht.buckets) in
    let len = Array.length old_buckets in 
    for i = 0 to len - 1 do
      let bucket = old_buckets.(i) in
      List.iter (fun (k, v) -> insert new_ht k v) bucket
    done;
    ht.buckets := !(new_ht.buckets);
    ht.capacity := !(new_ht.capacity);
    ht.size := !(new_ht.size)
      
     
  let get ht k = 
    let hs = Hashtbl.hash k in
    let bnum = hs mod !(ht.capacity) in 
    let bucket = !(ht.buckets).(bnum) in
    let res = List.find_opt (fun (k', _) -> k' = k) bucket in
    match res with 
    | Some (_, v) -> Some v
    | _ -> None

  (* Slow remove - introduce for completeness *)
  let remove ht k = 
    let hs = Hashtbl.hash k in
    let bnum = hs mod !(ht.capacity) in 
    let bucket = !(ht.buckets).(bnum) in
    let clean_bucket = 
      List.filter (fun (k', _) -> k' <> k) bucket in
    !(ht.buckets).(bnum) <- clean_bucket;
    (if List.length bucket > List.length clean_bucket
    then ht.size := !(ht.size) - 1);
    assert (!(ht.size) >= 0)


  let print_hash_table ppk ppv ht = 
    let open Printf in
    print_endline @@ sprintf "Capacity: %d" !(ht.capacity);
    print_endline @@ sprintf "Size:     %d" !(ht.size);
    print_endline "Buckets:";
    let buckets = !(ht.buckets) in
    for i = 0 to !(ht.capacity) - 1 do
      let bucket = buckets.(i) in
      if bucket <> [] then (
        (* Print bucket *)
        let s = List.fold_left 
            (fun acc (k, v) -> acc ^ (sprintf "(%s, %s); ") (ppk k) (ppv v)) "" bucket in
        printf "%d -> [ %s]\n" i s)
    done 
end;;

module RHT = ResizableListBasedHashTable(IntString);;
module ResizableHTTester = HashTableTester(RHT);;

(* open Week_12_BST;; *)
module BinarySearchTree =
  struct
    type 'e tree_node = {
        value : 'e;
        parent  : 'e tree_node option ref;
        left  : 'e tree_node option ref;
        right  : 'e tree_node option ref;
      }

    type 'e tree = {
        root : 'e tree_node option ref;
        size : int ref
      }

    let left n = !(n.left)
    let right n = !(n.right)
    let parent n = !(n.parent)
    let get_root t = !(t.root)
    let get_size t = !(t.size)

    let mk_node e = 
      {value = e;
       parent = ref None;
       left = ref None;
       right = ref None}
        
    let mk_tree _ = {root = ref None; size = ref 0}    
                      
    let map_option o f z = match o with
      | None -> z
      | Some n -> f n
                    

    (**********************************)
    (*     2. Growing the tree        *)
    (**********************************)
                    
    let insert t e =       
      let rec insert_element n e = 
        let m = mk_node e in
        if e < n.value
        then match left n with
             | Some m -> insert_element m e
             | None ->
                m.parent := Some n;
                n.left := Some m;
                true
        else if e > n.value
        then match right n with
             | Some m -> insert_element m e
             | None ->
                m.parent := Some n;
                n.right := Some m;
                true
        else false
      in
      match !(t.root) with
      | None -> (
        t.root := Some (mk_node e);
        t.size := 1;
        true)
      | Some n -> 
         if insert_element n e
         then (t.size := !(t.size) + 1; true)
         else false
                
                
    (**********************************)
    (*     2.5 Tree invariant         *)
    (**********************************)

    let check_bst_inv t = 
      let rec walk node p = 
        (p node.value) &&
          let res_left = match left node with
            | None -> true
            | Some l -> walk l (fun w -> p w && w <= node.value)
          in
          let res_right = match right node with
            | None -> true
            | Some r -> walk r (fun w -> p w && w >= node.value)
          in
          res_left && res_right
      in
      match !(t.root) with
      | None -> true
      | Some n -> walk n (fun _ -> true)

    (**********************************)
    (*     3. Printing a tree         *)
    (**********************************)

    let print_tree pp snum t = 
      let print_node_with_spaces l s = 
        for i = 0 to s - 1 do 
          Printf.printf " "
        done;
        print_endline (pp l.value);
      in

      let rec walk s node = match node with
        | None -> ()
        | Some n -> begin
            walk (s + snum) (right n);
            print_node_with_spaces n s;
            walk (s + snum) (left n);
          end      
      in
      map_option (get_root t) (fun n -> walk 0 (Some n)) ()
                 
    (**********************************)
    (*     4. Exploring the tree      *)
    (**********************************)

    let search t k = 
      let rec walk k n = 
        let nk = n.value in 
        if k = nk then Some n
        else if k < nk
        then match left n with
             | None -> None
             | Some l -> walk k l
        else match right n with
             | None -> None
             | Some r -> walk k r
      in
      map_option (get_root t) (walk k) None

    (**********************************)
    (* 5. Traversing a tree with DFS  *)
    (**********************************)

    open DLLBasedQueue

    let depth_first_search_rec t = 
      let rec walk q n =
        enqueue q n.value;
        (match left n with
         | Some l -> walk q l
         | None -> ());
        (match right n with
         | Some r -> walk q r
         | None -> ());
      in
      let acc = (mk_queue 0) in
      map_option (get_root t) (walk acc) ();
      queue_to_list acc

    let depth_first_search_loop t = 
      let open ListBasedStack in
      let loop stack q =
        while not (is_empty stack) do
          let n = get_exn @@ pop stack in
          enqueue q n.value;
          (match right n with
           | Some r -> push stack r
           | _ -> ());
          (match left n with
           | Some l -> push stack l
           | _ -> ());
        done
      in
      let acc = (mk_queue 0) in
      let stack = mk_stack 0 in
      (match get_root t with
       | None -> ()
       | Some n -> begin
           push stack n;
           loop stack acc;
         end);      
      queue_to_list acc

    (**********************************)
    (* 6. Traversing a tree with BFS  *)
    (**********************************)

    let breadth_first_search_loop t = 
      let loop wlist q depth =
        while not (is_empty wlist) do
          let n = get_exn @@ dequeue wlist in
          enqueue q n.value;
          (match left n with
           | Some l -> enqueue wlist l
           | _ -> ());
          (match right n with
           | Some r -> enqueue wlist r
           | _ -> ());
        done
      in
      let acc = (mk_queue 0) in
      let wlist = mk_queue 0 in
      (match get_root t with
       | None -> ()
       | Some n -> begin
           enqueue wlist n;
           loop wlist acc 0;
         end);      
      queue_to_list acc

    let elements t = breadth_first_search_loop t

    (**********************************)
    (* 7.  Finding a minimum node     *)
    (**********************************)

    let rec find_min_node n = 
      match left n with
      | Some m -> find_min_node m
      | None -> n

    (* Question: how to find a successor of a node in a tree? *)

    (**********************************)
    (* 8.    Deletion of an element   *)
    (**********************************)

    (* Replacing node U by (optional) node V in T. *)
    let transplant t u v = 
      (match parent u with
       | None -> t.root := v
       | Some p -> 
          match left p with
          | Some l when u == l -> p.left := v
          | _ -> p.right := v);
      (* Update parent of v *)
      match v with 
      | Some n -> n.parent := parent u
      | _ -> ()

    (* Deleting the a node z from tree *)
    (* z must be in the tree *)
    let delete_node t z = 
      t.size := !(t.size) - 1;
      if left z = None
      then transplant t z (right z)
      else if right z = None
      then transplant t z (left z)
      else
        (* Finding the successor of `z` *)
        let z_right_child = (get_exn @@ right z) in
        let y = find_min_node z_right_child in
        (* Fact: `y` has no left child *)

        (if parent y <> None &&
              z != get_exn @@ parent y
         then 
           (*  If y is not immediately under z,
          replace y by its right subtree *)
           let x = right y in
           (transplant t y x;
            y.right := right z;
            (get_exn @@ right y).parent := Some y));

        (* Now `y` replaces `z` at its position *)
        transplant t z (Some y);
        y.left := !(z.left);
        (get_exn @@ left y).parent := Some y
                                           

    (**********************************)
    (* 9. Rotations and balanced tree *)
    (**********************************)

    let left_rotate t x =
      match right x with
      | None -> ()
      | Some y ->
         
         (* turn y's left subtree into x's right subtree *)
         x.right := left y;
         (if left y <> None
          then (get_exn @@ left y).parent := Some x);
         
         (* link x's parent to y *)
         y.parent := parent x;

         (match parent x with 
          | None -> t.root := Some y
          | Some p -> match left p with
                      | Some l when x == l ->
                         p.left := Some y
                      | _ ->
                         p.right := Some y);
         
         (* Make x the left child of y *)
         y.left := Some x;
         x.parent := Some y      
      
end;;

open BinarySearchTree;;

let print_kv_tree = print_tree 
                      (fun (k, v) -> Printf.sprintf "(%d, %s)" k v) 12;;

(* open GraphicUtil *)

#load "graphics.cma"
open Graphics

let origin = (400, 300)

let go_to_origin _ =
  let x = fst origin in
  let y = snd origin in
  moveto x y;
  set_color black

let draw_axes _ =
  let x = fst origin in
  let y = snd origin in
  set_color green;
  moveto 0 y;
  lineto (x * 2) y;
  moveto x 0;
  lineto x (y * 2);
  moveto x y;
  set_color black

let mk_screen _ = 
  open_graph " 800x600";
  draw_axes ()
    
let clear_screen _ =
  clear_graph ();
  draw_axes ()

(* open Points *)
let eps = 0.0000001

let (=~=) x y = abs_float (x -. y) < eps

let (<=~) x y = x =~= y || x < y

let (>=~) x y = x =~= y || x > y

let is_zero x = x =~= 0.0

type point = Point of float * float
                      
let get_x (Point (x, y)) = x
let get_y (Point (x, y)) = y
  
(* include GraphicUtil *)

let draw_point ?color:(color = Graphics.black) (Point (x, y)) = 
  let open Graphics in
  let (a, b) = current_point () in
  let ix = int_of_float x + fst origin in 
  let iy = int_of_float y + snd origin in 
  moveto ix iy;
  set_color color;
  fill_circle ix iy 3;
  moveto a b;
  set_color black

(*

TODO: Draw a point

*)

(* Some test points *)
module TestPoints = struct

  let p = Point (100., 150.)
  let q = Point (-50., 75.)
  let r = Point (50., 30.)
  let s = Point (75., 60.)
  let t = Point (75., 90.)

end

(* Move the point *)
let (++) (Point (x, y)) (dx, dy) = 
  Point (x +. dx, y +. dy)



(*

TODO:
- Draw multiple points.
- Draw a line.
- Draw a triangle.

*)

    
(************************************)
(*        Point as a vector         *)
(************************************)

let vec_length (Point (x, y)) = 
  sqrt (x *. x +. y *. y)
    
let draw_vector (Point (x, y)) = 
  let ix = int_of_float x + fst origin in 
  let iy = int_of_float y + snd origin in 
  go_to_origin ();
  Graphics.lineto ix iy;
  go_to_origin ()

(* Subtract vectors *)
let (--) (Point (x1, y1)) (Point (x2, y2)) = 
  Point (x1 -. x2, y1 -. y2)


(***************************************)
(* Scalar product and its applications *)
(***************************************)

(*

* Question: 
  What is the graphical interpretation of the dot-product?

*)

let dot_product (Point (x1, y1)) (Point (x2, y2)) = 
  x1 *. x2 +. y1 *. y2

let angle_between v1 v2 =
  let l1 = vec_length v1 in 
  let l2 = vec_length v2 in 
  if is_zero l1 || is_zero l2 then 0.0
  else
    let p = dot_product v1 v2 in
    let a = p /. (l1 *. l2) in
    assert (abs_float a <=~ 1.);
    acos a
 
(* To polar representation *)

let pi = 4. *. atan 1.

type polar = Polar of (float * float)

let polar_of_cartesian ((Point (x, y)) as p) = 
  let r = vec_length p in
  let phi = atan2 y x in
  let phi' = if phi =~= ~-.pi then phi +. pi *. 2. else phi in
  assert (phi' > ~-.pi && phi' <=~ pi);
  Polar (r, phi')

let cartesian_of_polar (Polar (r, phi)) = 
  let x = r *. cos phi in
  let y = r *. sin phi in
  Point (x, y)

let rotate_by_angle p a =
  let Polar (r, phi) = polar_of_cartesian p in
  let p' = Polar (r, phi +. a) in
  cartesian_of_polar p'

(*

TODO: Graphical experiments with the angles

* Rotate one vector to another
* How to determine the angle?
* Draw something cool using polar coordinates.

*)

(************************************)
(*          Cross-product           *)
(************************************)

let cross_product (Point (x1, y1)) (Point (x2, y2)) = 
  x1 *. y2 -. x2 *. y1

let sign p = 
  if p =~= 0. then 0
  else if p < 0. then -1 
  else 1

(* Where should we turning p *)
let dir_clock p1 p2 = 
  let prod = cross_product p1 p2 in 
  sign prod

(*

TODO: Determine the direction to rotate a point.

*)

let rotate_to p1 p2 = 
  let a = angle_between p1 p2 in
  let d = dir_clock p1 p2 |> float_of_int in 
  rotate_by_angle p1 (a *. d)

(* Determining turns *)

(*
 1 - turning right (clock-wise)
-1 - turning left  (counter-clock-wise)
 0 - no turn

*)
let direction p0 p1 p2 = 
  cross_product (p2 -- p0) (p1 -- p0) |> sign

(*
TODO: 
experiment with directions.

*)
      
(******************************************)
(*    Segments and operations on them     *)
(******************************************)

type segment = point * point

(* Draw a segment *)
let draw_segment ?color:(color = Graphics.black) (a, b) = 
  let open Graphics in 
  let (Point (ax, ay)) = a in
  let (Point (bx, by)) = b in
  draw_point ~color:color a;
  draw_point ~color:color b;
  let iax = int_of_float ax + fst origin in
  let iay = int_of_float ay + snd origin in
  moveto iax iay;
  set_color color;
  let ibx = int_of_float bx + fst origin in
  let iby = int_of_float by + snd origin in
  lineto ibx iby;
  go_to_origin ()


module TestSegments = struct
  include TestPoints
  let s0 = (q, p)
  let s1 = (p, s)
  let s2 = (r, s)
  let s3 = (r, t)
  let s4 = (t, p)
  let s5 = (Point (-100., -100.), Point (100., 100.))
  let s6 = (Point (-100., 100.), Point (100., -100.))
end

(*****************************************)
(*  Generating random points on segments *)
(*****************************************)

let gen_random_point f =
  let ax = Random.float f in
  let ay = Random.float f in
  let o = Point (f /. 2., f /. 2.) in 
  Point (ax, ay) -- o

let gen_random_segment f = 
  (gen_random_point f, gen_random_point f)

let gen_random_point_on_segment seg = 
  let (p1, p2) = seg in
  let Point (dx, dy) = p2 -- p1  in
  let f = Random.float 1. in  
  let p = p1 ++ (dx *. f, dy  *. f) in
  p


(******************************************)
(*              Collinearity              *)
(******************************************)

(* Checking if segments are collinear *)
let collinear s1 s2 = 
  let (p1, p2) = s1 in
  let (p3, p4) = s2 in 
  let d1 = direction p3 p4 p1 in
  let d2 = direction p3 p4 p2 in
  d1 = 0 && d2 = 0
  
(* Checking if a point is on a segment *)
let point_on_segment s p =
  let (a, b) = s in
  if not (collinear (a, p) (p, b)) 
  then false
  else 
    let Point (ax, ay) = a in
    let Point (bx, by) = b in
    let Point (px, py) = p in
    min ax bx <=~ px &&
    px <=~ max ax bx &&
    min ay by <=~ py &&
    py <=~ max ay by

(******************************************)
(*         Checking for intersections     *)
(******************************************)

(* Checking if two segments intersect on a segment *)

let intersect_as_collinear s1 s2 = 
  if not (collinear s1 s2) then false
  else
    let (p1, p2) = s1 in
    let (p3, p4) = s2 in
    point_on_segment s1 p3 ||
    point_on_segment s1 p4 ||
    point_on_segment s2 p1 ||
    point_on_segment s2 p2

(* Checking if two segments intersect *)
let segments_intersect s1 s2 = 
  if collinear s1 s2 
  then intersect_as_collinear s1 s2
  else
    let (p1, p2) = s1 in
    let (p3, p4) = s2 in
    let d1 = direction p3 p4 p1 in
    let d2 = direction p3 p4 p2 in
    let d3 = direction p1 p2 p3 in
    let d4 = direction p1 p2 p4 in
    if (d1 < 0 && d2 > 0 || d1 > 0 && d2 < 0) &&
       (d3 < 0 && d4 > 0 || d3 > 0 && d4 < 0)
    then true
    else if d1 = 0 && point_on_segment s2 p1
    then true
    else if d2 = 0 && point_on_segment s2 p3
    then true
    else if d3 = 0 && point_on_segment s1 p3
    then true
    else if d4 = 0 && point_on_segment s1 p4
    then true
    else false

(******************************************)
(*      Finding intersection points       *)
(******************************************)


(* Finding an intersection point of two 
   non-collinear intersecting segments *)
let find_intersection s1 s2 = 
  let (p1, p2) = s1 in
  let (p3, p4) = s2 in
  
  if not (segments_intersect s1 s2) then None
  else if collinear s1 s2 
  then
    if point_on_segment s1 p3 then Some p3
    else if point_on_segment s1 p4 then Some p4
    else if point_on_segment s2 p1 then Some p1
    else Some p2        
  else
    let r = Point (get_x p2 -. get_x p1, get_y p2 -. get_y p1) in
    let s = Point (get_x p4 -. get_x p3, get_y p4 -. get_y p3) in
    assert (not @@ is_zero @@ cross_product r s);
    
    (*
     (p1 + t r) × s = (p3 + u s) × s,

      s x s = 0, hence 

      t = (p3 − p1) × s / (r × s)
    *)
    
    let t = (cross_product (p3 -- p1) s) /. (cross_product r s) in
    let Point (rx, ry) = r in
    let p = p1 ++ (rx *. t, ry *. t) in
    Some p

(* open Polygons *)
(* Some utility functions *)
let rec all_pairs ls = match ls with
  | [] -> []
  | _ :: [] -> []
  | h1 :: h2 :: t -> (h1, h2) :: (all_pairs (h2 :: t))    

let rec all_triples ls = 
  let (a, b) = (List.hd ls, List.hd @@ List.tl ls) in
  let rec walk l = match l with
    | x :: y :: [] -> [(x, y, a); (y, a, b)]
    | x :: y :: z :: t -> (x, y, z) :: (walk (y :: z :: t))    
    | _ -> []
  in
  assert (List.length ls >= 3);
  walk ls

(* Remove duplicates *)
let uniq lst =
  let seen = Hashtbl.create (List.length lst) in
  List.filter (fun x -> let tmp = not (Hashtbl.mem seen x) in
                        Hashtbl.replace seen x ();
                        tmp) lst


(******************************************)
(*             Polygons                   *)
(******************************************)

type polygon = point list 

let polygon_of_int_pairs l = 
  List.map (fun (x, y) -> 
      Point (float_of_int x, float_of_int y)) l

let shift_polygon (dx, dy) pol = 
  List.map (function Point (x, y) ->
    Point (x +. dx, y +. dy)) pol


(******************************************)
(*             Render Polygons            *)
(******************************************)

let draw_polygon ?color:(color = Graphics.black) p = 
  let open Graphics in
  set_color color;
  List.map (function Point (x, y) -> 
    (int_of_float x + fst origin, 
     int_of_float y + snd origin)) p |>
  Array.of_list |>
  draw_poly;
  set_color black

(******************************************)
(*             Test Polygons              *)
(******************************************)

module TestPolygons = struct

  let triangle = 
    [(-50, 50); (200, 0); (200, 200)] |> polygon_of_int_pairs

  let square = [(100, -100); (100, 100); (-100, 100); (-100, -100)] |> polygon_of_int_pairs

  let convexPoly2 = [(100, -100); (200, 200); (0, 200); (0, 0)] |> polygon_of_int_pairs

  let convexPoly3 = [(0, 0); (200, 0); (200, 200); (40, 100)] |> polygon_of_int_pairs

  let simpleNonConvexPoly = [(0, 0); (200, 0); 
                             (200, 200); (100, 50)] |> polygon_of_int_pairs

  let nonConvexPoly5 = [(0, 0); (0, 200); 
                        (200, 200); (-100, 300)] |> 
                       polygon_of_int_pairs |>
                       shift_polygon (-50., -100.)

  let bunnyEars  = [(0, 0); (400, 0); (300, 200); 
                    (200, 100); (100, 200)] |> 
                   polygon_of_int_pairs |>
                   shift_polygon (-100., -50.)

  let lShapedPolygon = [(0, 0); (200, 0); (200, 100); 
                        (100, 100); (100, 300); (0, 300)]  
                       |> polygon_of_int_pairs
                       |> shift_polygon (-150., -150.)

  let kittyPolygon = [(0, 0); (500, 0); (500, 200); 
                      (400, 100); (100, 100); (0, 200)] 
                     |> polygon_of_int_pairs
                     |> shift_polygon (-250., -150.)

  let simpleStarPolygon = [(290, 0); (100, 100); (0, 290); 
                           (-100, 100); (-290, 0); (-100, -100); 
                           (0, -290); (100, -100)]  |> polygon_of_int_pairs

  let weirdRectPolygon = [(0, 0); (200, 0); (200, 100); (100, 100); 
                          (100, 200); (300, 200); (300, 300); (0, 300)]  
                         |> polygon_of_int_pairs
                         |> shift_polygon (-150., -150.)

  let sand4 = [(0, 0); (200, 0); (200, 100); (170, 100); 
               (150, 40); (130, 100); (0, 100)] 
              |> polygon_of_int_pairs
              |> shift_polygon (-30., -30.)

  let tHorror = [(100, 300); (200, 100); (300, 300); 
                 (200, 300); (200, 400)]  
                |> polygon_of_int_pairs
                |> shift_polygon (-250., -250.)


  let chvatal_comb = [(500, 200); (455, 100); (400, 100);
                      (350, 200); (300, 100); (250, 100);
                      (200, 200); (150, 100); (100, 100);
                      (50, 200); (0, 0); (500, 0)]
                     |> polygon_of_int_pairs
                     |> shift_polygon (-200., -70.)
                       

  let chvatal_comb1 = [(500, 200); (420, 100); (400, 100);
                       (350, 200); (300, 100); (250, 100);
                       (200, 200); (150, 100); (100, 100);
                       (50, 200); (0, 70); (500, 70)]  
                      |> polygon_of_int_pairs
                      |> shift_polygon (-200., -70.)

  let shurikenPolygon = [(390, 0); (200, 50); (0, 290); 
                         (50, 150); (-200, -100); (0, 0)]  
                        |> polygon_of_int_pairs
                        |> shift_polygon (-80., -70.)


                                      
end

(******************************************)
(*       Manipulating with polygons       *)
(******************************************)

let resize_polygon k pol = 
  List.map (function Point (x, y) ->
    Point (x *. k, y *. k)) pol

(* What if k is negative? *)

let rotate_polygon pol p0 angle = 
  pol |>
  List.map (fun p -> p -- p0) |>
  List.map polar_of_cartesian |>
  List.map (function Polar (r, phi) -> 
      Polar (r, phi +. angle)) |>
  List.map cartesian_of_polar |>
  List.map (fun p -> p ++ (get_x p0, get_y p0))

(******************************************)
(*         Queries about polygons         *)
(******************************************)


(* Checking whether a polygon is convex *)
let is_convex pol = 
  all_triples pol |>
  List.for_all (fun (p1, p2, p3) -> direction p1 p2 p3 <= 0)

(* TODO: Check the tests *)

(* Detecting collisions *)

let edges pol = 
  if pol = [] then []
  else 
    let es = all_pairs pol in
    let lst = List.rev pol |> List.hd in
    let e = (lst, List.hd pol) in
    e :: es

let polygons_touch_or_intersect pol1 pol2 =
  let es1 = edges pol1 in
  let es2 = edges pol2 in
  List.exists (fun e1 ->
    List.exists (fun e2 -> 
          segments_intersect e1 e2) es2) es1

(* Question: what is the complexity of this? *)

(* TODO:

Play with multiple polygons, e.g., scaled and rotated kitty
*)

(******************************************)
(*        Intersection with a ray         *)
(******************************************)

type ray = point * float

let draw_ray ?color:(color = Graphics.black) r = 
  let (p, phi) = r in
  let open Graphics in
  let q = p ++ (2000. *. (cos phi), 2000. *. (sin phi)) in
  draw_segment ~color (p, q)

let point_on_ray ray p = 
  let (q, phi) = ray in
  (* Ray's direction *)
  let r = Point (cos phi, sin phi) in
  let u = dot_product (p -- q) r in
  u >=~ 0.

let ray_segment_intersection ray seg = 
  let (p, p') = seg in
  let (q, phi) = ray in
  (* Segment's direction *)
  let s = Point (get_x p' -. get_x p, get_y p' -. get_y p) in
  (* Ray's direction *)
  let r = Point (cos phi, sin phi) in

  if cross_product s r =~= 0. then
    if cross_product (p -- q) r =~= 0.
    then if point_on_ray ray p then Some p 
      else if point_on_ray ray p' then Some p'
      else None
    else None
  else begin
    (* Point on segment *)
    let t = (cross_product (q -- p) r) /. (cross_product s r) in
    (* Point on ray *)
    let u = (cross_product (p -- q) s) /. (cross_product r s) in
    if u >=~ 0. && t >=~ 0. && t <=~ 1. 
    then
      let Point (sx, sy) = s in
      let z = p ++ (sx *. t, sy *. t) in
      Some z
    else
      None
  end


(******************************************)
(*        Point within an polygon         *)
(******************************************)

(* Get neightbors of a vertex *)
let get_vertex_neighbours pol v = 
  assert (List.mem v pol);

  let arr = Array.of_list pol in
  let n = Array.length arr in
  assert (Array.length arr >= 3);

  if v = arr.(0) then (arr.(n - 1), arr.(1))
  else if v = arr.(n - 1) then (arr.(n - 2), arr.(0))
  else let rec walk i = 
         if i = n - 1 then (arr.(n - 2), arr.(0))
         else if v = arr.(i) 
         then (arr.(i - 1), arr.(i + 1))
         else walk (i + 1)
    in walk 1

(* Get neightbors of a vertex *)
let neighbours_on_different_sides ray pol p =
  if not (List.mem p pol) then true
  else
    let (a, b) = get_vertex_neighbours pol p in
    let (r, d) = ray in 
    let s = r ++ (cos d, sin d) in
    let dir1 = direction r s a in
    let dir2 = direction r s b in
    dir1 <> dir2


(* Point within a polygon *)

let choose_ray_angle pol = 
  let edge_angles = 
    edges pol |>
    List.map (fun (Point (x1, y1), Point (x2, y2)) -> 
        let dx = x2 -. x1 in
        let dy = y1 -. y1 in 
        atan2 dy dx) in
  let n = List.length pol in
  let candidate_angles = 
    iota (n + 1) |>
    List.map (fun i -> 
      (float_of_int i) *. pi /. (float_of_int n)) in
  let phi = List.find (fun c ->  List.for_all 
                          (fun a -> not (a =~= c)) 
                          edge_angles) candidate_angles in
  phi

  let point_within_polygon pol p = 
    let ray = (p, (choose_ray_angle pol)) in
    let es = edges pol in
    if List.mem p pol ||
       List.exists (fun e -> point_on_segment e p) es then true
    else
      begin
        let n = 
          edges pol |> 
          List.map (fun e -> ray_segment_intersection ray e) |>
          List.filter (fun r -> r <> None) |>
          List.map (fun r -> get_exn r) |>
  
          (* Touching edges *)
          uniq |>
  
          (* Touching vertices *)
          List.filter (neighbours_on_different_sides ray pol) |>
  
          (* Compute length *)
          List.length
        in
        n mod 2 = 1
      end

(* open ConvexHulls *)
(*************************************)
(*        Auxiliary opoerations      *)
(*************************************)

module StackX (S: AbstractStack) = struct
  include S

  let top s = match pop s with
    | None -> None
    | Some x ->
      push s x;
      Some x

  let next_to_top s = match pop s with
    | None -> None
    | Some x -> 
      let y = top s in
      push s x;
      y

  let list_of_stack s = 
    let res = ref [] in
    while not (is_empty s) do
      let e = get_exn @@ pop s in
      res := e :: !res
    done;
    !res

end


(*************************************)
(*        Convex hull                *)
(*************************************)

(* Sort by axis Y *)
let axis_y_sorter (Point (x1, y1)) (Point (x2, y2)) =
  if y1 < y2 then -1 else if y1 > y2 then 1
  else if x1 < x2 then -1 else if x1 > x1 then 1
  else 0

(* Sort by polar angle wrt p0 *)
let polar_angle_sorter p0 p1 p2 = 
  let Polar (r1, a1) = p1 -- p0 |> polar_of_cartesian in
  let Polar (r2, a2) = p2 -- p0 |> polar_of_cartesian in
  if a1 < a2 then -1 else if a1 > a2 then 1
  else if r1 < r2 then -1 else if r1 > r2 then 1 
  else 0

module CHStack = StackX(ListBasedStack)

(* Graham's Scan *)
let convex_hull points = 
  (* At least three points *)
  assert (List.length points >= 3);

  let y_sorted = List.sort axis_y_sorter points in
  let p0 = y_sorted |> List.hd in 
  let p1 :: p2 :: rest = List.tl y_sorted |> 
                         List.sort (polar_angle_sorter p0) in
  let open CHStack in
  (* let open Week_01 in *)
  let s = mk_stack 0 in
  push s p0;
  push s p1;
  push s p2; 
  
  let non_left_turn p = 
    let q1 = next_to_top s |> get_exn in
    let q2 = top s |> get_exn in
    direction q1 q2 p >= 0
  in
  
  (* Main algorithm *)
  List.iter (fun p ->
      while non_left_turn p do
        let _ = pop s in ()
      done;
      push s p) rest;
  
  list_of_stack s 

(* Question: what is the complexity *)
    
(*************************************)
(*        Testing Convex hulls       *)
(*************************************)

let gen_random_points ?dim:(dim = 550.) n = 
  let res = ref [] in
  for _ = 0 to n - 1 do
    let p = gen_random_point dim in
    res := p :: !res
  done;
  !res
    

(*************************************)
(*     Tracing convex hulls          *)
(*************************************)

let draw_stack_and_points s ps p = 
  let open CHStack in
  if is_empty s then ()
  else begin
    let l = list_of_stack s in 
    List.iter (fun e -> push s e) l;
    let ll = all_pairs l in
    List.iter draw_point ps;
    List.iter (draw_segment ~color:Graphics.red) ll;
    Unix.sleepf 0.5
  end
  

let convex_hull_with_tracing ?cur:(cur = false) points = 
  (* At least three points *)
  assert (List.length points >= 3);

  let y_sorted = List.sort axis_y_sorter points in
  let p0 = y_sorted |> List.hd in 
  let p1 :: p2 :: rest = List.tl y_sorted |> 
                         List.sort (polar_angle_sorter p0) in
  let open CHStack in
  (* let open Week_01 in *)
  let s = mk_stack 0 in
  push s p0;
  push s p1;
  push s p2; 
  
  let non_left_turn p = 
    let q1 = next_to_top s |> get_exn in
    let q2 = top s |> get_exn in
    direction q1 q2 p >= 0
  in
  
  List.iter (fun p ->
      while non_left_turn p do
        let _ = pop s in ()
      done;
      push s p;

      clear_screen ();    
      (if cur then draw_segment ~color:Graphics.blue (p0, p));
      draw_stack_and_points s points p) rest;
  
  let res = list_of_stack s in
  
  clear_screen ();
  List.iter draw_point points;
  draw_polygon ~color:Graphics.red res;
  
  res *)
