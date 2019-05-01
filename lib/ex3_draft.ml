(* open Week_01 *)
(* open Week_02 *)
(* open Week_03 *)
(* open Week_06 *)
(* open GraphicUtil *)
(* open Points *)
(* open Polygons *)
(* open ConvexHulls *)
#use "ex3_libraries.ml";;
#use "ex3_rooms.ml";;

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
  let candidates = [Point (x +. 1., y); Point (x +. 1., y +. 1.); Point (x, y +. 1.); Point (x -. 1., y +. 1.); Point (x -. 1., y); Point (x -. 1., y -. 1.); Point (x, y -. 1.); Point (x +. 1., y -. 1.)] in
  let neighbours = List.filter (fun e -> square_inside_room room e) candidates in
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

(* greedy & fixed order *)
let get_watchman_path room =
  let p = ref (Point (0., 0.)) in
  let path = ref [!p] in
  let neighbours = ref (get_lightable_neighbours room !p) in
  let all_squares = get_all_squares room in
  let num_of_squares = List.length all_squares in
  let open SquareTable in
  let lighted_squares = mk_new_table 5 in
  List.iter (fun e -> insert lighted_squares e true) (uniq (!p :: !neighbours));
  let preferences = [|"up"; "right"; "down"; "left"|] in
  while (!(lighted_squares.size) < num_of_squares) do
    let next_move = choose_next_move room !p preferences lighted_squares in
    if next_move <> None
    then
      begin
        p := get_exn next_move;
        neighbours := get_lightable_neighbours room !p;
        path := !p :: !path;
        List.iter (fun e -> insert lighted_squares e true) (uniq (!p :: !neighbours));
      end
    else
      (* TBD *)
      (* if we are trapped, restart procedure at an unlighted square *)
      ();
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


(************************************************)
(*                3. Output file                *)
(************************************************)


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
  (--) (Point (400., 300.)) (Point (dx *. scaling_factor, dy *. scaling_factor));;

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
  clear_graph ();
  let origin = get_origin room in
  let scaling_factor = get_scaling_factor room in
  draw_room room;
  Thread.delay 1.;
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
  while (!(lighted_squares.size) < num_of_squares) do
    Thread.delay 1.;
    let next_move = choose_next_move room !p preferences lighted_squares in
    if next_move <> None
    then
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
    else
      (* TBD *)
      (* if we are trapped, restart procedure at an unlighted square *)
      ();
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
play_game room1;;
play_game room2;;
