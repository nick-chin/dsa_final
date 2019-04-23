open Week_01
open Week_06
open Week_13_Paths
open Week_02

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
    List.iter  (fun n -> insert parent_map n None) all_nodes;

     let helper g s =
    (*Make color of s gray*)
    insert color_map s Gray;
    (*Make distance of s Finite 0)*)
    insert distance_map s (Finite 0);
    (*Make parent of S None*)
    insert parent_map s root;


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
          insert parent_map v u;
          enqueue q v;
          end
        else if v_color = Gray
        then begin
            let v' = ref (get parent_map v) in
            let u' = ref (get parent_map u) in
            while get_exn !v' <> get_exn !u' do
				insert parent_map v (get parent_map (get_exn !v'));
				v' := get parent_map v;
				u' := get parent_map (get_exn !u')
            done
          end
        else if v_color = Black
        then begin
			let dist_v = int_of_distance @@ get_exn @@ get distance_map v in
			let dist_u = int_of_distance @@ get_exn @@ get distance_map u in
			let v' = ref (get parent_map v) in
            let u' = ref (get parent_map u) in
			for _ = 1 to dist_u - dist_v do
				u' := get parent_map (get_exn !u')
			done;
            while get_exn !v' <> get_exn !u' do
				insert parent_map v (get parent_map (get_exn !v'));
				v' := get parent_map v;
				u' := get parent_map (get_exn !u')
            done;
			insert distance_map v (get_exn @@ get distance_map (get_exn !v'))
          end);
               insert color_map u Black;
    done in


(* We iterate through all the nodes with white color after the queue gets empty*)

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
         let dst = get_exn @@ get_exn @@ get p_map h in
         if dst = h
         then ()
         else add_edge g h dst;
         add_edges t
    in
    add_nodes nodes;
    add_edges nodes;
    g
     
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
  (root, read_graph_and_payloads n nodes edges' weights);;


 
