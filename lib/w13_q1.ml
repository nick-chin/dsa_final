open Week_01
open Week_06
open Week_13_Paths

open Week_12_Graphs
open Week_13_Reachability
open Week_12_BST
open BinarySearchTree
open LinkedGraphs

module GraphBFS = struct
  open NodeTable
  open Distance
  open DLLBasedQueue

  type color = White | Gray | Black

  let  bfs g =

    let color_map = mk_new_table (v_size g) in
    let parent_map = mk_new_table (v_size g) in
    let tree_map = mk_new_table (v_size g) in
    let distance_map = mk_new_table (v_size g) in
    let has_cycles = ref false in
    let roots = ref [] in
    let all_nodes = get_nodes g in

    (* Make all nodes white *)
    List.iter  (fun n -> insert color_map n White) all_nodes;
    (* Make all distances Infinity *)
    List.iter  (fun n -> insert distance_map n Infinity) all_nodes ;
    (*Make the parent of each node None*)
    List.iter  (fun n -> insert parent_map n None) all_nodes ;
    (*Initialize tree map*)
    List.iter (fun n -> insert tree_map n []) all_nodes;

     let helper g s =
    (*Make color of s gray*)
    insert color_map s Gray;
    (*Make distance of s Finite 0)*)
    insert distance_map s (Finite 0);
    (*Make parent of S None*)
    insert parent_map s (None);


    (* Make a queue *)
    let q = mk_queue (v_size g) in
    (*Enuqueue (q,s)*)
    enqueue q s;


    while not (is_empty q) do
     let u = get_exn (dequeue q) in

(*Perform action on all adjacent vertices*)

(*Whenever a white vertex is found while scanning the adjacent vertices to u, the vertex v
and the edge (u, v) are added to the tree.*)
    get_succ g u |> List.iter (fun v ->
        let v_color = get_exn @@ get color_map v in
        if v_color = White
        then begin
          insert color_map v Gray;
          insert distance_map v ((get_exn @@ get distance_map u) + Finite 1);
          insert parent_map v (Some u);
          let siblings = get_exn @@ get tree_map u in
          insert tree_map u (v :: siblings);
          enqueue q v;
          end
        else if v_color = Gray
        then has_cycles := true
        else if v_color = Black
        then has_cycles := true);
      insert color_map u Black;
   done in


(* We iterate through all the nodes with white color after the queue gets empty*)

      all_nodes |> List.iter (fun n ->
        if get_exn @@ get color_map n = White
        then begin
          (* Record roots *)
          roots := n :: !roots;
          helper g n
        end);
    (!roots, parent_map, distance_map, tree_map)
    
    (* Visualise with BFS *)
let graphviz_with_bfs g out =
let (_, _, _, tree) = bfs g in
let eattrib (s, d) = match get tree s with
  | None -> ""
  | Some p ->
    if List.mem d p
    then bold_edge
    else ""
in
let open Week_10_ReadingFiles in
let ag = LinkedGraphs.to_adjacency_graph g in
let s = graphviz_string_of_graph "digraph" " -> "
    string_of_int eattrib ag in
write_string_to_file out s

end



(*Procedure to generate random graph*)


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
    end)) all_nodes;;


let gen_random_rooted_graph n =
  let g = mk_graph() in
  let node_root = gen_nodes n in
  let nodes =  fst (node_root) in
  let root = snd (node_root) in
  let edges = gen_edges n in
  addnodes nodes g;
  addedges edges g;
  ensure_reachability g n root;
  (root, g);;
  
  
  (*Helper functions for Tests*)
  
  open GraphBFS
  
  let is_reachable_via_bfs g init final =
  let (roots, _, _, tree) = bfs g in
  let rec walk n =
    if n = final then true
    else
      NodeTable.get tree n |>
      Week_01.get_exn |>
      List.exists (fun v -> walk v)
  in
  if List.mem init roots
  then walk init
  else false
  
  
let equ list1 list2 = 
  let rec as_mem l1 l2 = 
  match l1 with
  | [] -> true
  | h :: t -> List.mem h l2 && as_mem t l2
  in
  List.length list1 = List.length list2 && as_mem list1 list2
  
  
  (*Test for bfs*)


let test_bfs g =
  let all_nodes = LinkedGraphs.get_nodes g in
  let (bfs_roots, _, _, _) = GraphBFS.bfs g in

  (* Any node BFS-reachable from a root r is reachable from r *)
  let fact1 =
    List.for_all (fun u ->
        (List.for_all  (fun v ->
            if is_reachable_via_bfs g u v
            then is_reachable g u v
            else true) all_nodes)) bfs_roots
  in

  (* Any node is reachable from some root r *)
  let fact2 =
    List.for_all (fun u ->
        (List.exists (fun r -> is_reachable_via_bfs g r u) bfs_roots))
          all_nodes in
          
   (* Roots of the trees we obtain from DFS search and BFS search are the same*)      
   let (dfs_roots, _, _, _) = GraphDFS.dfs g in
   let fact3 =  equ bfs_roots  dfs_roots in

  fact1 && fact2 && fact3




