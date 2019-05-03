open Week_01
open Week_02
open Week_06
open Week_12_BST
open Week_12_Graphs
open Week_13_Paths
open Week_13_Reachability
open BinarySearchTree
open LinkedGraphs


(***************************************************************)
(* Part 1: Generating a Sentinel Tree from a rooted Graph      *)
(***************************************************************)
   

module GraphSentinel = struct
  open NodeTable
  open Distance
  open DLLBasedQueue

  type color = White | Black

  let sentinel_tree ((root: int), g) =
    let color_map = mk_new_table (v_size g) in
    let parent_map = mk_new_table (v_size g) in
    let distance_map = mk_new_table (v_size g) in
    let all_nodes = get_nodes g in

    (* Make all nodes white *)
    List.iter  (fun n -> insert color_map n White) all_nodes;
    (* Make the parent of each node the root by default *)
    (* Parent is defined as immediate sentinel for every node besides the root, which is updated later *)
    List.iter  (fun n -> insert parent_map n root) all_nodes;

     let helper g s =
    (* Note that s is the root *)

    (* Make color of s Black *)
    insert color_map s Black;
    (* Make distance of s Finite 0 *)
    insert distance_map s (Finite 0);
    (* Make parent of s the Root *)
    insert parent_map s root;


    (* Make a queue *)
    let q = mk_queue (v_size g) in
    (* Enuqueue (q, s) *)
    enqueue q s;

    while not (is_empty q) do
      let u = get_exn (dequeue q) in

      (* Perform action on all adjacent vertices *)
      (* We follow the process depending on the color of the sucessor *)
      get_succ g u |> List.iter (fun v ->
          let v_color = get_exn @@ get color_map v in
          if v_color = White
          then
            begin
              insert color_map v Black;
              insert distance_map v ((get_exn @@ get distance_map u) + Finite 1);
              insert parent_map v u;
              enqueue q v
            end
          else
            begin
              let dist_v =  get_exn @@ get distance_map v in
              let dist_u =  get_exn @@ get distance_map u in
              let v' = ref (get parent_map v) in
              let u' = ref (get parent_map u) in
              if dist_v > dist_u
              then
                for _ = 1 to ((int_of_dist @@ dist_v) - (int_of_dist @@ dist_u)) do
	          v' := get parent_map (get_exn !v')
                done
              else if dist_v < dist_u
              then
                for _ = 1 to ((int_of_dist @@ dist_u) - (int_of_dist @@ dist_v)) do
	          u' := get parent_map (get_exn !u')
                done;
              while get_exn !v' <> get_exn !u' do
                v' := get parent_map (get_exn !v');
		u' := get parent_map (get_exn !u');
              done;
              insert parent_map v (get_exn !v');
              insert distance_map v (Finite 1 + (get_exn @@ get distance_map (get_exn !v')))
            end);
      insert color_map u Black;
    done in

     (* Run the helper function in our root*)
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




(***************************************************************)
(* Part 2: Generating Random Rooted Directed Graphs            *)
(***************************************************************)



(*Procedure to generate random graph*)


let gen_nodes n = let arr = Array.make n "0" in
  let root = (Random.int (n -1)) in
  for i = 0 to n - 1 do
    arr.(i) <- string_of_int(i);
  done;
  (arr, root)

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


let addnodes (lst: string array) g =
  let len = Array.length lst in
  for i = 0 to len -1  do
    add_node g lst.(i);
  done

let addedges (lst: (int * int) array) g =
  let len = Array.length lst in
  for i = 0 to len -1  do
    add_edge g (fst (lst.(i))) (snd (lst.(i)));
  done
  
  
let ensure_reachability graph root =
  let all_nodes = get_nodes graph in
  List.iter (fun x -> if x = root then () else
                begin
                  if not (is_reachable graph root x)
                  then add_edge graph root x
                end) all_nodes


(*Main Function: Procedure to generate random rooted graph*)

let gen_random_rooted_graph n =
  let g = mk_graph() in
  let node_root = gen_nodes n in
  let nodes =  fst (node_root) in
  let root = snd (node_root) in
  let edges = gen_edges n in
  addnodes nodes g;
  addedges edges g;
  ensure_reachability g root;
  (root, g)



(***************************************************************)
(* Part 3: Tests for our Main Algorithm                        *)
(***************************************************************)

(*Tests by generating random Paths*)

(*Depth First Search Modified: suitable for a rooted graph*)

module DFSRooted = struct
  open NodeTable

  type color = White | Gray | Black

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
end


(*Gives random element from a list*)

let randomelement l =
    List.nth l (Random.int (List.length l))


(* Generates random path in a rooted from the root to any other node*)

let gen_path_list (root, g) =
  let open DFSRooted in
  let open NodeTable in
  let a = dfs_changed g root in
  let sec t = match t with
      (_, b, _, _) -> b in
  let table = sec a in
  let path_current = ref (get_exn @@ get table root) in
  let path_list = ref [root] in
  while !path_current  != [] do
    let rand = randomelement !path_current in
    path_list := rand:: !path_list;
    path_current := get_exn @@ get table rand;
  done;
  !path_list



(* Returns the sentinels of a given node, say a, in a graph, as a list*)


let gen_strict_sentinels a root table  =
  let open NodeTable in
  let sentinel = ref (get_exn @@ get table a) in
  let sentinel_list = ref [!sentinel] in
  while !sentinel != root do
    sentinel := get_exn @@ get table !sentinel;
    sentinel_list := !sentinel :: !sentinel_list
  done;
  !sentinel_list


(*Test for sentinel property *)

open GraphSentinel

let test_for_sentinel_property (root, g) n =
  let success = ref true in
  for i= 0 to (Random.int n) do
    let list_paths = gen_path_list (root, g) in
    let rec check_sentinel_property_each  list_of_path=
      match list_of_path with
      | [] -> success := true && !success
      | h::t-> let sentinels_of_h = gen_strict_sentinels h root (snd @@ sentinel_tree (root, g)) in
      (List.iter (fun x ->
                     success := !success && (List.mem x list_of_path)) sentinels_of_h) in
    check_sentinel_property_each list_paths
  done;
  !success

let example_graph =
    	([|"a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"; "k"|],
    	[(0, 1); (1, 2); (2, 3); (2, 4); (2, 5); (3, 4); (3, 6); (4, 7); (4, 8);
    	(5, 9); (6, 3); (7, 10); (8, 3); (9, 1); (9, 2); (10, 2)])

let example_graphe = read_graph_and_payloads 11 (fst example_graph) (snd example_graph) ([] : (int * int * unit) list)

let sentinel_of_example = sentinel_tree (0, example_graphe)


let test_for_example_graph () =
  let open NodeTable in
  get_exn @@ get (snd sentinel_of_example) 1 == 0 &&
  get_exn @@ get (snd sentinel_of_example) 2 == 1 &&
  get_exn @@ get (snd sentinel_of_example) 3 == 2 &&
  get_exn @@ get (snd sentinel_of_example) 4 == 2 &&
  get_exn @@ get (snd sentinel_of_example) 5 == 2 &&
  get_exn @@ get (snd sentinel_of_example) 6 == 3 &&
  get_exn @@ get (snd sentinel_of_example) 7 == 4 &&
  get_exn @@ get (snd sentinel_of_example) 8 == 4 &&
  get_exn @@ get (snd sentinel_of_example) 9 == 5 &&
  get_exn @@ get (snd sentinel_of_example) 10 == 7


let final_test () =
  (test_for_sentinel_property (gen_random_rooted_graph 6) 4) &&
    (test_for_sentinel_property (0, (example_graphe)) 4) &&
      test_for_example_graph ()
