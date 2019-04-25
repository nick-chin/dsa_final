open Week_01
open Week_02
open Week_06
open Week_13_Paths
open Week_12_Graphs
open Week_13_Reachability
open Week_12_BST
open BinarySearchTree
open LinkedGraphs


module GraphSentinel = struct
  open NodeTable
  open Distance
  open DLLBasedQueue

  type color = White | Gray | Black

  let sentinel_tree ((root: int), g) =

    let color_map = mk_new_table (v_size g) in
    let parent_map = mk_new_table (v_size g) in
    let distance_map = mk_new_table (v_size g) in
    let all_nodes = get_nodes g in

    (* Make all nodes white *)
    List.iter  (fun n -> insert color_map n White) all_nodes;
    (*Make the parent of each node None*)
    List.iter  (fun n -> insert parent_map n root) all_nodes;

     let helper g s =
    (*Make color of s gray*)
    insert color_map s Gray;
    (*Make distance of s Finite 0)*)
    insert distance_map s (Finite 0);
    (*Make parent of S the root*)
    insert parent_map s root;


    (* Make a queue *)
    let q = mk_queue (v_size g) in
    (*Enuqueue (q,s)*)
    enqueue q s;


    while not (is_empty q) do
     let u = get_exn (dequeue q) in

(*Perform action on all adjacent vertices*)

(*For all adjacent vertices of u, we check for the immediate sentinel*)
    get_succ g u |> List.iter (fun v ->
        let v_color = get_exn @@ get color_map v in
        if v_color = White
        then begin
          insert color_map v Gray;
          insert distance_map v ((get_exn @@ get distance_map u) + Finite 1);
          insert parent_map v u;
          enqueue q v;
          end
        else if v_color = Gray
        then begin
            let v' = ref (get parent_map v) in
            let u' = ref (get parent_map u) in
            while get_exn !v' <> get_exn !u' do
				insert parent_map v (get_exn @@ get parent_map (get_exn !v'));
				v' := get parent_map v;
				u' := get parent_map (get_exn !u')
            done;
            insert distance_map v (Finite 1 + (get_exn @@ get distance_map (get_exn !v')))
          end
        else if v_color = Black
        then begin
			let dist_v = int_of_dist @@ get_exn @@ get distance_map v in
			let dist_u = int_of_dist @@ get_exn @@ get distance_map u in
			let v' = ref (get parent_map v) in
            let u' = ref (get parent_map u) in
			for _ = 1 to dist_u - dist_v do
				u' := get parent_map (get_exn !u')
			done;
            while get_exn !v' <> get_exn !u' do
				insert parent_map v (get_exn @@ get parent_map (get_exn !v'));
				v' := get parent_map v;
				u' := get parent_map (get_exn !u')
            done;
			insert distance_map v (Finite 1 + (get_exn @@ get distance_map (get_exn !v')))
          end);
               insert color_map u Black;
    done in


(* We perform the function on the root*)

     helper g root;
     (all_nodes, parent_map)

  let visualize_sentinel_tree (nodes, p_map) =
    let open LinkedGraphs in
    let g = mk_graph () in
    let rec add_nodes ls =
      match ls with
      | [] -> ()
      | h :: t ->
         add_node g h;
         add_nodes t
    in
    let rec add_edges ls =
      match ls with
      | [] -> ()
      | h :: t ->
         let dst = get_exn @@ get p_map h in
         if dst = h
         then ()
         else add_edge g dst h;
         add_edges t
    in
    add_nodes nodes;
    add_edges nodes;
    g

end




(*Procedure to generate random graph - helper functions*)

let gen_nodes n = let arr = Array.make n "0" in
let root = (Random.int (n -1)) in
for i = 0 to n - 1 do
arr.(i) <- string_of_int(i);
done;
(arr, root);;

let gen_edges n =
  let size = Random.int (n* n) in
  let max = n - 1 in
  let gen_edges_helper size_list max_num  =
    let arr = Array.make size_list (0,0) in
    for i = 0 to size_list - 1 do
      arr.(i) <-  (Random.int  max_num, Random.int  max_num)
    done;
    arr;
  in gen_edges_helper size max


let addnodes (lst: string array) g = let len = Array.length lst in
   for i = 0 to len -1  do
   add_node g lst.(i);
   done


let addedges (lst: (int * int) array) g = let len = Array.length lst in
     for i = 0 to len -1  do
     add_edge g (fst (lst.(i))) (snd (lst.(i)));
     done

let ensure_reachability graph n root =
  let max = n - 1 in
  let all_nodes = get_nodes graph in
  List.iter (fun x -> if x = root then () else
  (begin
    while not (is_reachable graph root x) do
      (*let an_edge = (Random.int max, Random.int max) in
      add_edge graph (fst (an_edge)) (snd (an_edge));*)
      let an_edge = (root, Random.int max) in
         add_edge graph (fst (an_edge)) (snd (an_edge));
         add_edge graph (snd (an_edge)) x;
      done;
    end)) all_nodes


(*Procedure to generate random rooted graph*)

let gen_random_rooted_graph n =
  let g = mk_graph() in
  let node_root = gen_nodes n in
  let nodes =  fst (node_root) in
  let root = snd (node_root) in
  let edges = gen_edges n in
  addnodes nodes g;
  addedges edges g;
  ensure_reachability g n root;
  (root, g)


(*Procedure to generate random rooted graph with weights*)

let gen_rnd_root_graphviz n =
  let g = mk_graph() in
  let node_root = gen_nodes n in
  let nodes =  fst (node_root) in
  let root = snd (node_root) in
  let edges = gen_edges n in
  addnodes nodes g;
  addedges edges g;
  ensure_reachability g n root;
  let open AdjacencyGraphs in
  let g' = to_adjacency_graph g in
  let edges' = edges g' in
  let weights = List.map (fun (x, y) -> (x, y, 1)) edges' in
  Printf.printf "Root is %d" root;
  (root, read_graph_and_payloads n nodes edges' weights)


(*Tests by generating random Paths*)
open GraphSentinel
open NodeTable

(*Depth First Search adapted for a rooted graph*)




let rec dfs_changed g root =
  let color_map = mk_new_table (v_size g) in
  let tree_map = mk_new_table (v_size g) in
  let time_map = mk_new_table (v_size g) in
  let has_cycles = ref false in
  let roots = ref [] in
  let all_nodes = get_nodes g in

  (* Make all nodes white *)
  List.iter (fun n -> insert color_map n White) all_nodes;
  (* Insert all nodes to the tree *)
  List.iter (fun n -> insert tree_map n []) all_nodes;

  let time = ref 0 in

  let rec dfs_visit u =
    time := !time + 1;
    let u_in = !time in
    insert color_map u Gray;
    get_succ g u |> List.iter (fun v ->
        let v_color = get_exn @@ get color_map v in
        if v_color = White
        then begin
          let siblings = get_exn @@ get tree_map u in
          insert tree_map u (v :: siblings);
          dfs_visit v
        end
        else if v_color = Gray
        then has_cycles := true) ;
    insert color_map u Black;
    time := !time + 1;
    let u_out = !time in
    insert time_map u (u_in, u_out)
  in
 dfs_visit root;
(!roots, tree_map, time_map, !has_cycles)


(*Gives random element from a list- saves space in the main function*)


let randomelement l =
    List.nth l (Random.int (List.length l))


(* Generates random path in a rooted graph from the root to any other node by doing 1 round of dfs*)

let gen_path_list (root, g) =
  let a = dfs_changed g root in
  let sec t = match t with
  (_, b, _, _) -> b in
  let table = sec a in
  let path_current = ref ( get_exn @@ get table root) in
  let path_list = ref [root] in
  while !path_current  != [] do
    let rand = randomelement !path_current in
    path_list := rand:: !path_list;
    path_current := get_exn @@ get table rand;
  done;
!path_list



(* Checks the sentinels of a given node, say a, in a graph*)


let gen_strict_sentinels a root table  =
  let sentinel = ref (get_exn @@ get table a) in
  let sentinel_list = ref [!sentinel] in
  while !sentinel != root do
    sentinel := get_exn @@ get table !sentinel;
    sentinel_list := !sentinel :: !sentinel_list
  done;
  !sentinel_list


(*Test for sentinel property *)

let test_for_sentinel_property (root, g) n=
  let success = ref true in
  for i= 0 to (Random.int n) do
    let list_paths = gen_path_list (root, g) in
    let rec check_sentinel_property_each  list_of_path=
      match list_of_path with
      | [] -> success := true && !success
      | h::t-> let sentinels_of_h = gen_strict_sentinels h root (snd @@ sentinel_tree (root, g)) in
      (List.iter (fun x -> x;
                     success := !success && (List.mem x list_of_path)) sentinels_of_h) in
    check_sentinel_property_each list_paths
  done;
  !success
  
  
