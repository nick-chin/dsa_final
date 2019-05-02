open Week_01
open Week_02
open Week_03
open Week_06
open Week_08_HashTable
open GraphicUtil
open Graphics
open Points
open Polygons
open Watchman_rooms

module Astar :
sig
  type 'a t =
    {
      cost : 'a -> 'a -> int;
      goal : 'a;
      get_next_states : 'a -> 'a list;
    }
  (* search function takes two arguments 'problem' and 'start'
  and returns a path (a list of points) from 'start' to
  [problem.goal]. The path minimizes [problem.cost]. *)
  val search : 'a t -> 'a -> 'a list
end = struct
  type 'a t = (* problem *)
    {
      cost : 'a -> 'a -> int;
      goal : 'a;
      get_next_states : 'a -> 'a list;
    }

  type 'a path =
    {
      cost_from_start : int; (** the cost from the start to [head]. *)
      total_cost : int; (** the total cost from the start to the goal (estimated). *)
      head : 'a; (* can think of this as the current position? *)
      tail : 'a list; (* the rest of path from head to start *)
    }

  let create_path ?from problem state = (* ?from:'a path -> 'a t -> 'a -> 'a path *)
    let (cost_from_start, tail) = match from with (* from is 'a path option *)
      | None -> (0, [])
      | Some p -> (p.cost_from_start + problem.cost p.head state, (* existing cost + cost from the head to a state *)
                    p.head :: p.tail) (* add head to tail, which is points we have traversed *)
    in
    let total_cost = cost_from_start + problem.cost state problem.goal in
    { cost_from_start; total_cost; tail; head = state}

  (** [better p q] returns [true] if path [p] is better than path [q]. *)
  let better p q = p.total_cost < q.total_cost (* 'a path -> 'b path -> bool *)

  (** [pickup_eq_path p l] returns [Some (q, l')] where [q] is the path that
      indicates the same position as [p] and [l] is a list excluding [q]. *)
  let pickup_eq_path p l = (* 'a path -> 'a path list -> ('a path * 'a path list) option *)
    match List.partition (fun q -> p.head = q.head) l with
    | [], _ -> None
    | [q], l' -> Some (q, l')
    | _ -> raise (Failure "duplicated paths in open/close list")

  (** [trace_next_states problem open_list close_list path] traces the next
      states of [path.head] and return [(open_list', close_list')] where [open_list'] and [close_list']
      are respectively an open list and a close list after all of the next
      states are traced. *)
  let trace_next_states problem ol0 cl0 path0 = (* 'a t -> 'a path list -> 'a path list -> 'a path -> 'a path list * 'a path list *)
    let trace_state (ol, cl) state =
      let path = create_path ~from:path0 problem state in
      match pickup_eq_path path ol with
      | Some (q, ol') -> if better path q then (path :: ol', cl) else (ol, cl)
      | None ->
        match pickup_eq_path path cl with
        | Some (q, cl') -> if better path q then (path :: ol, cl') else (ol, cl)
        | None -> (path :: ol, cl)
    in
    List.fold_left trace_state (ol0, cl0) (problem.get_next_states path0.head)

  (* [pickup_best_path l] returns [Some (p, l')] where [p] is the path that
      has the least cost in [l] and [l'] is an open list without [p]. *)
  (* takes a list of paths - open list *)
  let pickup_best_path = function (* 'a path list -> ('a path * 'a path list) option *)
    | [] -> None
    | h :: t ->
      let aux (y, l) x = if better y x then (y, x :: l) else (x, y :: l) in
      Some (List.fold_left aux (h, []) t)

  let search problem start = (* 'a t -> 'a -> 'a list *)
    let rec aux (ol, cl) = (* open and close lists are lists of paths *)
      match pickup_best_path ol with
      | None -> None (* No path reaches to [problem.goal] *)
      | Some (p, ol') ->
        if p.head = problem.goal then Some p (* reached to the goal *)
        else aux (trace_next_states problem ol' (p :: cl) p) (* putting the path with least cost into close list, and remove from open list *)
    in
    match aux ([create_path problem start], []) with
    | None -> raise Not_found
    | Some p -> p.head :: p.tail
end

(************************************************)
(*               1. Main function               *)
(************************************************)
(* get the maximum element in a list *)
let max_list l =
  List.fold_left (fun acc x -> max acc x) (float_of_int min_int) l;;

(* get the minimum element in a list *)
let min_list l =
  List.fold_left (fun acc x -> min acc x) (float_of_int max_int) l;;

(* check if a 1 x 1 square given by p (its left-bottom corner) is inside the room *)
let square_inside_room room p =
  point_within_polygon room ((++) p (0.5, 0.5));;

let get_neighbours room p =
    let Point (x, y) = p in
    let candidates = [Point (x +. 1., y); Point (x +. 1., y +. 1.); Point (x, y +. 1.); Point (x -. 1., y +. 1.); Point (x -. 1., y); Point (x -. 1., y -. 1.); Point (x, y -. 1.); Point (x +. 1., y -. 1.)] in
    let neighbours = List.filter (fun e -> square_inside_room room e) candidates in
    neighbours
    
(* get all the squares inside the room, given by their lower left corners *)
let get_all_squares room =
  let all_x = List.map (fun e -> get_x e) room in
  let all_y = List.map (fun e -> get_y e) room in
  let (min_x, min_y) = (min_list all_x, min_list all_y) in
  let (max_x, max_y) = (max_list all_x, max_list all_y) in
  let res = ref [] in
  let x = ref min_x in
  while !x < max_x do
    let y = ref min_y in
    while !y < max_y do
      let p = Point (!x, !y) in
      if square_inside_room room p
      then
        res := p :: !res;
      y := !y +. 1.
    done;
    x := !x +. 1.
  done;
  !res;;

(* get the Euclidean distance between two points *)
let distance a b =
  vec_length ((--) a b);;

(* get the neighbours of a square p inside the room that can be reached by light *)
let get_lightable_neighbours room p =
  let Point (x, y) = p in
  let neighbours = get_neighbours room p in
  (* check if a neighbour is lightable from p (light cannot go around corners) *)
  let lightable p neighbour =
    if neighbour = Point (x +. 1., y +. 1.)
    then
      (List.mem (Point (x +. 1., y)) neighbours) && (List.mem (Point (x, y +. 1.)) neighbours)
    else if neighbour = Point (x +. 1., y -. 1.)
    then
      (List.mem (Point (x +. 1., y)) neighbours) && (List.mem (Point (x, y -. 1.)) neighbours)
    else if neighbour = Point (x -. 1., y -. 1.)
    then
      (List.mem (Point (x -. 1., y)) neighbours) && (List.mem (Point (x, y -. 1.)) neighbours)
    else if neighbour = Point (x -. 1., y +. 1.)
    then
      (List.mem (Point (x -. 1., y)) neighbours) && (List.mem (Point (x, y +. 1.)) neighbours)
    else
      true
  in
  let lightable_neighbours = List.filter (fun e -> lightable p e) neighbours in
  lightable_neighbours;;

(* get the possible moves from a square p inside the room *)
let get_next_moves room p =
  let Point (x, y) = p in
  let candidates = [Point (x +. 1., y); Point (x, y +. 1.); Point (x -. 1., y); Point (x, y -. 1.)] in
  let next_moves = List.filter (fun e -> square_inside_room room e) candidates in
  next_moves;;

(* hash table to record lighted squares *)
module SquareTable =
  ResizableListBasedHashTable(struct type t = point * bool end);;
(* hash table to record direction priorities *)
module PrefTable =
  ResizableListBasedHashTable(struct type t = point * int end);;

(* count the number of new squares lighted by moving to point p *)
let count_new_lighted_squares room lighted_squares p =
  let neighbours = get_lightable_neighbours room p in
  let check_lighted value =
    match value with
    | None -> false
    | _ -> true
  in let open SquareTable in
  let new_lighted = List.filter (fun e -> not (check_lighted (get lighted_squares e))) neighbours in
  List.length new_lighted;;

(* check if moving to point p lights up new squares *)
let light_new_squares room lighted_squares p =
    count_new_lighted_squares room lighted_squares p <> 0;;

(* compare two moves by the number of potential newly lighted squares in reverse order *)
let comp_move_new_lighted room lighted_squares p1 p2 =
  let new1 = count_new_lighted_squares room lighted_squares p1 in
  let new2 = count_new_lighted_squares room lighted_squares p2 in
  if new1 < new2 then 1
  else if new1 > new2 then (-1)
  else 0;;

(* build a hashtable out of a list of directions in the order of preference priority *)
let get_pref_table preferences p =
  let open PrefTable in
  let pref_table = mk_new_table 4 in
  for i = 0 to 3 do
    let direction = preferences.(i) in
    if direction = "up"
    then insert pref_table ((++) p (0., 1.)) i
    else if direction = "right"
    then insert pref_table ((++) p (1., 0.)) i
    else if direction = "down"
    then insert pref_table ((++) p (0., -1.)) i
    else if direction = "left"
    then insert pref_table ((++) p (-1., 0.)) i
  done;
  pref_table;;

(* choose the next move greedily, and if two moves potentially light the same number of new squares, choose according to a priority list of directions; if we cannot light new squares by moving in any of the four directions, we return None to indicate that we are trapped and the procedure needs to restart in another (possibly distant) unlighted square *)
let choose_next_move room p preferences lighted_squares =
  let next_moves = get_next_moves room p in
  let open PrefTable in
  let pref_table = get_pref_table preferences p in
  match List.sort (comp_move_new_lighted room lighted_squares) next_moves with
  | h1 :: h2 :: t ->
     if light_new_squares room lighted_squares h1
     then
       let new1 = count_new_lighted_squares room lighted_squares h1 in
       let new2 = count_new_lighted_squares room lighted_squares h2 in
       if new1 = new2
       then
         let priority1 = get pref_table h1 in
         let priority2 = get pref_table h2 in
         if priority1 < priority2
         then Some h1
         else Some h2
       else
         Some h1
     else None
  | [h] ->
     if light_new_squares room lighted_squares h
     then Some h
     else None
  | _ -> None;;

module PointTable = ResizableListBasedHashTable(struct type t = Point end);;

(* greedy & fixed order *)
let get_watchman_path room =
  let open Astar in
  let open PointTable in
  let p = ref (Point (0., 0.)) in
  let path = ref [!p] in
  let neighbours = ref (get_lightable_neighbours room !p) in
  let all_squares = get_all_squares room in
  let num_of_squares = List.length all_squares in
  let open SquareTable in
  let lighted_squares = mk_new_table 5 in
  List.iter (fun e -> insert lighted_squares e true) (uniq (!p :: !neighbours));
  let preferences = [|"up"; "right"; "down"; "left"|] in
  let solve field init final =
    match (init, final) with
    | start, goal ->
      let cost p q =
        let Point (i,j) = p in
        let Point (k,l) = q in 
        Float.to_int(Float.abs (i-.k) +. Float.abs (j-.l)) in
      let problem = {cost; goal; get_next_states = get_next_moves field} in
      let lst = search problem start in
      let rec walk ls acc =
        match ls with
        | [] -> acc
        | h :: t ->
          if light_new_squares room lighted_squares h
          then h :: acc
          else walk t (h :: acc)
      in List.rev (walk (List.rev lst) [])
  in
  let closest_square lst current =
  let dst = ref None in
  let res = ref None in
  let rec find_closest_square ls = 
    match ls with
    | [] -> ()
    | h :: t -> if get lighted_squares h <> None then find_closest_square t else 
      let Point (i,j) = h in
      let Point (k,l) = current in
      let dst' = Float.to_int(Float.abs (i-.k) +. Float.abs (j-.l)) in
      if !dst = None then 
      begin
        dst := Some dst';
        res := Some h
      end
      else if dst' < get_exn (!dst) then
      begin
        dst := Some dst';
        res := Some h
      end
      else ();
      find_closest_square t
    in 
    find_closest_square lst;
    !res
  in
  while (!(lighted_squares.size) < num_of_squares) do (* when the room is not fully lit *)
    let next_move = choose_next_move room !p preferences lighted_squares in
    if next_move = None
    then
    begin
      let c = closest_square all_squares !p in
      if c <> None 
      then begin
        let closest_path = solve room !p (get_exn c) in
        List.iter (fun x -> 
          p := x;
          neighbours := get_lightable_neighbours room !p;
          path := !p :: !path;
          List.iter (fun e -> insert lighted_squares e true) (uniq (!p :: !neighbours))) (List.tl closest_path);
      end
      else ()
    end
    else
      begin
        p := get_exn next_move;
        neighbours := get_lightable_neighbours room !p;
        path := !p :: !path;
        List.iter (fun e -> insert lighted_squares e true) (uniq (!p :: !neighbours));
      end
  done;
  List.rev !path;;

(*
open TestRooms;;
let room = room1;;
let p = ref (Point (0., 0.));;
let path = ref [!p];;
let neighbours = ref (get_lightable_neighbours room !p);;
let all_squares = get_all_squares room;;
let num_of_squares = List.length all_squares;;
open SquareTable;;
let lighted_squares = mk_new_table 5;;
List.iter (fun e -> insert lighted_squares e true) (uniq (!p :: !neighbours));;
let preferences = [|"up"; "right"; "down"; "left"|];;
(!(lighted_squares.size) < num_of_squares);;
let next_move = choose_next_move room !p preferences lighted_squares;;
next_move <> None;;
p := get_exn next_move;;
neighbours := get_lightable_neighbours room !p;;
path := !p :: !path;;
List.iter (fun e -> insert lighted_squares e true) (uniq (!p :: !neighbours));;
List.rev !path;;
 *)
  
(************************************************)
(*                   2. Tests                   *)
(************************************************)
(* path starts at (0, 0) *)
let test_start_at_origin path =
  List.hd path = Point (0., 0.);;

(* path is connected *)
let test_connectivity room path =
  let rec walk path' acc =
    match path' with
    | h1 :: h2 :: t ->
       walk (h2 :: t) ((List.mem h2 (get_neighbours room h1)) && acc)
    | _ -> acc
  in
  walk path true;;

(* path does not go through the walls or go outside the room *)
let test_no_collisions room path =
  (* it suffices to check that all squares that the watchman stepped on in the path are inside the room *)
  List.for_all (fun e -> square_inside_room room e) path;;

(* the whole room is lighted in the end *)
let test_full_room_coverage room path =
  let open SquareTable in
  let rec walk path' lighted_squares =
    match path' with
    | h :: t ->
       begin
         let neighbours = get_lightable_neighbours room h in
         List.iter (fun e -> insert lighted_squares e true) (uniq (h :: neighbours));
         walk t lighted_squares
       end
    | [] -> lighted_squares
  in
  let lighted = walk path (mk_new_table 5) in
  let num_of_squares = List.length (get_all_squares room) in
  !(lighted.size) = num_of_squares;;


(* test if the path is valid *)
let test_valid_path room =
  let p = get_watchman_path room in
  assert (test_start_at_origin p);
  assert (test_connectivity room p);
  assert (test_no_collisions room p);
  assert (test_full_room_coverage room p);
  true;;

(* get the edges of a polygon *)
let get_edges polygon =
  let rec walk poly edges =
    match poly with
    | h1 :: h2 :: t ->
       walk (h2 :: t) ((h1, h2) :: edges)
    | _ -> edges
  in
  walk polygon [];;


(* randomly choose the next point in the polygon *)
let generate_next_point p edgeLength =
  let p1 = ref p in
  let seed = Random.int 3 in
  if seed = 0
  then
    (* go right *)
    p1 := (++) p (edgeLength, 0.)
  else if seed = 1
  then
    (* go up *)
    p1 := (++) p (0., edgeLength)
  else if seed = 2
  then
    (* go down *)
    p1 := (++) p (0., -.edgeLength)
  else
    (* go left *)
    p1 := (++) p (-.edgeLength, 0.);
  !p1;;


(* generate a random polygon containing the square (0, 0) in the first quadrant *)
let generate_random_polygon n turnsLimit =
  let p = ref (Point (0., 0.)) in
  let p1 = ref !p in
  let polygon = ref [!p] in
  let turns = ((Random.int (turnsLimit/2)) + 2) * 2 in
  let edgeLimit = n in
  for i = 0 to turns do
    let edgeLength = float_of_int ((Random.int edgeLimit) + 1) in
    if i <> 0
    then
      begin
        (* as long as p1 is outside the first quadrant, or the new edge (p, p1) intersects with the polygon, or (p, p1) is collinear with the previous edge, pick again *)
        while (not (List.for_all (fun e -> find_intersection (!p, !p1) e = None)
                      (List.tl (get_edges (List.rev !polygon))))) ||
                (collinear (!p, !p1) (List.hd (List.tl !polygon), !p)) ||
                  (((<=~) (get_x !p1) 0.) || ((<=~) (get_y !p1) 0.)) do
          let edgeLength = float_of_int ((Random.int edgeLimit) + 1) in
          p1 := generate_next_point !p edgeLength;
        done;
      end
    else
      (* go right at the first step *)
      p1 := Point (edgeLength, 0.);
    polygon := !p1 :: !polygon;
    p := !p1
  done;
  (* go back to origin *)
  let ending_point = List.hd !polygon in
  (* if going all the way left from the ending point does not intersect the polygon *)
  if List.for_all (fun e -> not (segments_intersect (ending_point, Point (0., get_y ending_point)) e)) (get_edges !polygon)
  then polygon := (Point (0., get_y ending_point)) :: !polygon
  else
    begin
      let high_point = Point (get_x ending_point, (max_list (List.map (fun e -> get_y e) !polygon)) +. 5.) in
      if collinear (high_point, ending_point) (ending_point, List.hd (List.tl !polygon))
      then polygon := List.tl !polygon
      else ();
      polygon := (Point (0., get_y high_point)) :: high_point :: !polygon;
    end;
  List.rev (!polygon);;

(* flip a polygon vertically *)
let flip poly =
  List.map (fun e -> if (=~=) (get_y e) 0. then Point (get_x e, 0.) else Point (get_x e, -.(get_y e))) poly;;


(* generate a random room *)
let generate_random_room _ =
  let poly1 = generate_random_polygon 10 20 in
  let poly2 = generate_random_polygon 10 30 in
  let flipped_poly2 = flip poly2 in
  let len1 = List.length poly1 in
  let len2 = List.length poly2 in
  let p = gen_random_point_on_segment (List.nth poly1 (len1 - 2), List.nth poly1 (len1 - 1)) in
  let shifted_poly2 = List.map (fun e -> (++) e (float_of_int (int_of_float (get_x p)), float_of_int (int_of_float (get_y p +. get_y (List.nth poly2 (len2 - 1)))))) flipped_poly2 in
  let rec walk l1 l2 acc =
    match l1 with
    | [] -> acc
    | [h] ->
       (match l2 with
       | [] -> h :: acc
       | h' :: t' -> walk [h] t' (h' :: acc))
    | h :: t -> walk t l2 (h :: acc)
  in
  let final_poly = List.tl @@ List.rev shifted_poly2 in
  List.rev (walk poly1 (final_poly @ [List.nth shifted_poly2 (len2 - 1)]) []);;

        
(* random rooms test *)

let test_random_rooms _ =
  for _ = 1 to 5 do
    let room = generate_random_room () in
    assert (test_valid_path room)
  done;
  true;;
(************************************************)
(*                3. Output file                *)
(************************************************)
open TestRooms
open Week_10_ReadingFiles
open Batteries
let get_solution_as_string room = 
  let path = get_watchman_path room in
  let rec convert p = 
    match p with
    | [] -> []
    | Point (i,j) :: t -> (Printf.sprintf "(%d, %d)" (Float.to_int i) (Float.to_int j)) :: convert t
    in 
  String.concat "; " (convert path)

let room_list = [room1; room2; room3; room4; room5; room6; room7; room8; room9; room10]

let get_solution_list ls filename =
  let i = ref 0 in
  let s_lst = List.map (fun x -> i := !i + 1; string_of_int !i ^ ": " ^ get_solution_as_string x) ls in
  write_strings_to_file filename s_lst;;



  




(************************************************)
(*                4. Explanation                *)
(************************************************)
(* see report *)


(************************************************)
(*               5. Visualization               *)
(************************************************)

(* draw blank window without axes *)
let draw_canvas _ = open_graph " 800x600";;

(* get the scaling factor that best visualizes the room *)
let get_scaling_factor room =
  let all_x = List.map (fun e -> get_x e) room in
  let all_y = List.map (fun e -> get_y e) room in
  let (min_x, min_y) = (min_list all_x, min_list all_y) in
  let (max_x, max_y) = (max_list all_x, max_list all_y) in
  let scaling_factor = 580. /. (max (max_x -. min_x) (max_y -. min_y)) in
  scaling_factor;;

(* get the position of the origin (0, 0) that best visualizes the room *)
let get_origin room =
  let scaling_factor = get_scaling_factor room in
  let all_x = List.map (fun e -> get_x e) room in
  let all_y = List.map (fun e -> get_y e) room in
  let (min_x, min_y) = (min_list all_x, min_list all_y) in
  let (max_x, max_y) = (max_list all_x, max_list all_y) in
  let center = (Point ((max_x +. min_x)/.2., (max_y +. min_y)/.2.)) in
  let Point (dx, dy) = center in
  Points.(--) (Point (400., 300.)) (Point (dx *. scaling_factor, dy *. scaling_factor))

(* shift a point with respect to the origin and scale it for visualization *)
let calibrate p scaling_factor origin =
  let Point (x0, y0) = origin in
  let x = x0 +. (get_x p) *. scaling_factor in
  let y = y0 +. (get_y p) *. scaling_factor in
  Point (x, y);;

(* get the center of the room *)
let get_center room =
  let origin = get_origin room in
  let scaling_factor = get_scaling_factor room in
  let all_x = List.map (fun e -> get_x e) room in
  let all_y = List.map (fun e -> get_y e) room in
  let (min_x, min_y) = (min_list all_x, min_list all_y) in
  let (max_x, max_y) = (max_list all_x, max_list all_y) in
  let center = (Point ((max_x +. min_x)/.2., (max_y +. min_y)/.2.)) in
  calibrate center scaling_factor origin;;

(* draw a room scaled by the scaling factor *)
let draw_room room =
  clear_graph ();
  let origin = get_origin room in
  let scaling_factor = get_scaling_factor room in
  set_color black;
  fill_poly (Array.of_list (List.map (fun e ->
                                let Point (x, y) = calibrate e scaling_factor origin in
                                (int_of_float x, int_of_float y)) room));;
(*
open TestRooms;;
draw_canvas ();;
draw_room room1;;
draw_room room2;;
draw_room room3;;
draw_room room4;;
draw_room room5;;
draw_room room6;;
draw_room room7;;
draw_room room8;;
draw_room room9;;
draw_room room10;;
clear_graph ();;
 *)


(* cast light in the 1 x 1 square whose left-bottom corner is p *)
let cast_light p scaling_factor origin =
  let Point (x, y) = calibrate p scaling_factor origin in
  let sf = int_of_float scaling_factor in
  set_color yellow;
  fill_rect (int_of_float x) (int_of_float y) sf sf;
  set_color black;
  draw_rect (int_of_float x) (int_of_float y) sf sf;;

(* return the center of a square given by its lower left corner (scaled) *)
let square_center p scaling_factor origin =
  let Point (x, y) = p in
  let center = Point (x +. 0.5, y +. 0.5) in
  calibrate center scaling_factor origin;;

(* check if a square given by its lower left corner is already lighted *)
let lighted p scaling_factor origin =
  let Point (x, y) = square_center p scaling_factor origin in
  point_color (int_of_float x) (int_of_float y) <> black;;

(* cast light around a watchman's position without letting the light go outside the room *)
let cast_light_around room p scaling_factor origin =
  let neighbours = get_lightable_neighbours room p in
  List.iter (fun e -> if (square_inside_room room e) && (not (lighted e scaling_factor origin))
                      then cast_light e scaling_factor origin) (p :: neighbours);;

(* draw a red line between points a and b (scaled) *)
let draw_line a b scaling_factor origin =
  set_color red;
  let a' = calibrate a scaling_factor origin in
  let b' = calibrate b scaling_factor origin in
  moveto (int_of_float (get_x a')) (int_of_float (get_y a'));
  lineto (int_of_float (get_x b')) (int_of_float (get_y b'));;

(* draw the watchman as a red dot in a square given by its lower left corner (scaled) *)
let draw_watchman p scaling_factor origin =
  set_color red;
  let Point (x, y) = square_center p scaling_factor origin in
  fill_circle (int_of_float x) (int_of_float y) (int_of_float (scaling_factor *. 0.3));;

(* remove the watchman from a square given by its lower left corner (scaled) *)
let remove_watchman p scaling_factor origin =
  set_color yellow;
  let Point (x, y) = square_center p scaling_factor origin in
  fill_circle (int_of_float x) (int_of_float y) (int_of_float (scaling_factor *. 0.3));;

(* visualize a watchman's route as he walks (scaled) *)

let visualize room =
  let open Astar in
  let open PointTable in
  clear_graph ();
  let origin = get_origin room in
  let scaling_factor = get_scaling_factor room in
  draw_room room;
  Thread.delay 0.3;
  let p = ref (Point (0., 0.)) in
  cast_light_around room !p scaling_factor origin;
  draw_watchman !p scaling_factor origin;
  let path = ref [!p] in
  let neighbours = ref (get_lightable_neighbours room !p) in
  let all_squares = get_all_squares room in
  let num_of_squares = List.length all_squares in
  let open SquareTable in
  let lighted_squares = mk_new_table 5 in
  List.iter (fun e -> insert lighted_squares e true) (uniq (!p :: !neighbours));
  let preferences = [|"up"; "right"; "down"; "left"|] in
  let solve field init final =
  match (init, final) with
  | start, goal ->
    let cost p q =
      let Point (i,j) = p in
      let Point (k,l) = q in 
      Float.to_int(Float.abs (i-.k) +. Float.abs (j-.l)) in
    let problem = {cost; goal; get_next_states = get_next_moves field} in
    let lst = search problem start in
    let rec walk ls acc =
      match ls with
      | [] -> acc
      | h :: t ->
        if light_new_squares room lighted_squares h
        then h :: acc
        else walk t (h :: acc)
    in List.rev (walk (List.rev lst) [])
  in
  let closest_square lst current =
  let dst = ref None in
  let res = ref None in
  let rec find_closest_square ls = 
    match ls with
    | [] -> ()
    | h :: t -> if get lighted_squares h <> None then find_closest_square t else 
      let Point (i,j) = h in
      let Point (k,l) = current in
      let dst' = Float.to_int(Float.abs (i-.k) +. Float.abs (j-.l)) in
      if !dst = None then 
      begin
        dst := Some dst';
        res := Some h
      end
      else if dst' < get_exn (!dst) then
      begin
        dst := Some dst';
        res := Some h
      end
      else ();
      find_closest_square t
    in 
    find_closest_square lst;
    !res
  in
  while (!(lighted_squares.size) < num_of_squares) do (* when the room is not fully lit *)
    Thread.delay 0.3;
    let next_move = choose_next_move room !p preferences lighted_squares in
    if next_move = None
    then
    begin
      let c = closest_square all_squares !p in
      if c <> None 
      then begin
        let closest_path = solve room !p (get_exn c) in
        List.iter (fun x ->
          Thread.delay 0.3;
          remove_watchman !p scaling_factor origin;
          draw_line ((++) !p (0.5, 0.5)) ((++) x (0.5, 0.5)) scaling_factor origin;
          cast_light_around room x scaling_factor origin;
          draw_watchman x scaling_factor origin; 
          p := x;
          neighbours := get_lightable_neighbours room !p;
          path := !p :: !path;
          List.iter (fun e -> insert lighted_squares e true) (uniq (!p :: !neighbours))) (List.tl closest_path);
      end
      else ()
    end
    else
      begin
        let p1 = get_exn next_move in
        remove_watchman !p scaling_factor origin;
        draw_line ((++) !p (0.5, 0.5)) ((++) p1 (0.5, 0.5)) scaling_factor origin;
        cast_light_around room p1 scaling_factor origin;
        draw_watchman p1 scaling_factor origin;
        p := p1;
        neighbours := get_lightable_neighbours room !p;
        path := !p :: !path;
        List.iter (fun e -> insert lighted_squares e true) (uniq (!p :: !neighbours));
      end
  done;
  List.rev !path;;

open TestRooms;;
(* cannot put mk_screen () inside the function, other wise will raise error:
Exception: (Unix.Unix_error "Interrupted system call" select "").
Raised by primitive operation at unknown location
Called from file "thread.ml", line 74, characters 23-50
Called from file "//toplevel//", line 265, characters 2-17
Called from file "toplevel/toploop.ml", line 180, characters 17-56
 *)
(*
draw_canvas ();;
visualize room1;;
clear_graph();;
 *)


(************************************************)
(*                6. Video game                 *)
(************************************************)
let play_game room =
  draw_canvas ();
  let origin = get_origin room in
  let scaling_factor = get_scaling_factor room in
  draw_room room;
  let p = ref (Point (0., 0.)) in
  let path = ref [!p] in
  let neighbours = ref (get_lightable_neighbours room !p) in
  let all_squares = get_all_squares room in
  let num_of_squares = List.length all_squares in
  let open SquareTable in
  let lighted_squares = mk_new_table 5 in
  List.iter (fun e -> insert lighted_squares e true) (uniq (!p :: !neighbours));
  cast_light_around room !p scaling_factor origin;
  draw_watchman !p scaling_factor origin;
  let rec play _ =
    if (!(lighted_squares.size) < num_of_squares)
    then
      begin
        let event = wait_next_event [Key_pressed] in
        draw_watchman !p scaling_factor origin;
        cast_light_around room !p scaling_factor origin;
        let p1 = ref !p in
        if event.key == 'w'
        then p1 := (++) !p (0., 1.)
        else if event.key == 's'
        then p1 := (++) !p (0., -1.)
        else if event.key == 'a'
        then p1 := (++) !p (-1., 0.)
        else if event.key == 'd'
        then p1 := (++) !p (1., 0.)
        else if event.key == 'q'
        then exit 0
        else
          play();
        if square_inside_room room !p1
        then
          begin
            remove_watchman !p scaling_factor origin;
            draw_line ((++) !p (0.5, 0.5)) ((++) !p1 (0.5, 0.5)) scaling_factor origin;
            cast_light_around room !p1 scaling_factor origin;
            draw_watchman !p1 scaling_factor origin;
            p := !p1;
            neighbours := get_lightable_neighbours room !p;
            path := !p :: !path;
            List.iter (fun e -> insert lighted_squares e true) (uniq (!p :: !neighbours));
            play ()
          end
        else
          play ()
      end
    else
      let score = List.length !path in
      (* let Point (cx, cy) = get_center room in
      let (x, y) = (int_of_float (cx -. scaling_factor), (int_of_float cy)) in
      moveto x y;
       *)
      set_text_size 12;
      set_color blue;
      draw_string ("GAME FINISHED. SCORE: "^(string_of_int score));
  in
  play ();
  !path;;

open TestRooms;;
(*play_game room1;;
play_game room2;;
*)