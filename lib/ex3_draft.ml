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

(* changed 0. to pi *)
let point_within_polygon1 pol p = 
  (* let ray = (p, 0.) in *)
  let ray = (p, Random.float pi) in
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
    end;;

(* 1. *)

(* get the maximum element in a list *)
let max_list l =
  List.fold_left (fun acc x -> max acc x) (float_of_int min_int) l;;

(* get the minimum element in a list *)
let min_list l =
  List.fold_left (fun acc x -> min acc x) (float_of_int max_int) l;;

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

(* get the neighbours of a square p inside the room *)
let get_neighbours room p =
  let Point (x, y) = p in
  let candidates = [Point (x +. 1., y); Point (x +. 1., y +. 1.); Point (x, y +. 1.); Point (x -. 1., y +. 1.); Point (x -. 1., y); Point (x -. 1., y -. 1.); Point (x, y -. 1.); Point (x +. 1., y -. 1.)] in
  let neighbours = List.filter (fun e -> square_inside_room room e) candidates in
  neighbours;;
  

let get_watchman_path room =
  let path = ref [Point (0., 0.)] in
  let lighted_squares = ref [Point (0., 0.)] in
  let all_squares = get_all_squares room in
  let neighbours = [Point (1., 0.); Point (1., 1.); Point (0., 1.)] in
  let rec loop ngbrs next =
    match ngbrs with
    | [] -> loop []
         
  
(* 5. Visualization *)
(* shift a point with respect to the origin (400, 300) and scale it for visualization *)
let calibrate p scaling_factor =
  let (x0, y0) = origin in
  let x = float_of_int (x0 + (int_of_float ((get_x p) *. scaling_factor))) in
  let y = float_of_int (y0 + (int_of_float ((get_y p) *. scaling_factor))) in
  Point (x, y);;

let draw_room room scaling_factor =
  let room_scaled = resize_polygon scaling_factor room in
  draw_polygon room_scaled;;

(* cast light in the 1 x 1 square whose left-bottom corner is p *)
let cast_light p scaling_factor =
  let Point (x, y) = calibrate p scaling_factor in
  let sf = int_of_float scaling_factor in
  set_color yellow;
  fill_rect (int_of_float x) (int_of_float y) sf sf;;

(* check if a 1 x 1 square given by p (its left-bottom corner) is inside the room *)
let square_inside_room room p =
  let Point (x, y) = p in
  let corners = [p; Point (x +. 1., y); Point (x +. 1., y +. 1.); Point (x, y +. 1.)] in
  let res = List.map (fun e -> point_within_polygon1 room e) corners in
  List.for_all (fun e -> e) res;;

(* return the center of a square given by its lower left corner *)
let square_center p scaling_factor =
  let Point (x, y) = p in
  let center = Point (x +. 0.5, y +. 0.5) in
  calibrate center scaling_factor;;

(* check if a square given by its lower left corner is already lighted *)
let lighted p scaling_factor =
  let Point (x, y) = square_center p scaling_factor in
  point_color (int_of_float x) (int_of_float y) = yellow;;

(* cast light around a watchman's position without letting the light go outside the room *)
let cast_light_around room p scaling_factor =
  let Point (x, y) = p in
  let corners = [Point (x, y); Point (x +. 1., y); Point (x +. 1., y +. 1.); Point (x, y +. 1.); Point (x -. 1., y +. 1.); Point (x -. 1., y); Point (x -. 1., y -. 1.); Point (x, y -. 1.); Point (x +. 1., y -. 1.)] in
  List.iter (fun e -> if (square_inside_room room e) &&
                           (not (lighted e scaling_factor)) then cast_light e scaling_factor) corners;;

(* draw a red line between points a and b (scaled) *)
let draw_line a b scaling_factor =
  set_color red;
  let a' = calibrate a scaling_factor in
  let b' = calibrate b scaling_factor in
  moveto (int_of_float (get_x a')) (int_of_float (get_y a'));
  lineto (int_of_float (get_x b')) (int_of_float (get_y b'));;

(* draw the watchman's route (scaled) *)
let draw_route route scaling_factor =
  let len = List.length route in
  let arr = Array.of_list route in
  for i = 0 to (len - 2) do
    draw_line arr.(i) arr.(i+1) scaling_factor
  done;;

(* visualize a watchman route in a room (scaled) *)
let visualize room route scaling_factor =
  (* List.iter (fun p -> cast_light_around room p) route;
  draw_route route;; *)
  let len = List.length route in
  let arr = Array.of_list route in
  for i = 0 to (len - 2) do
    Thread.delay 1.;
    cast_light_around room arr.(i) scaling_factor;
    draw_line arr.(i) arr.(i+1) scaling_factor
  done;
  cast_light_around room arr.(len - 1);;
                       
                              
open TestRooms;;
let route = List.map (fun e -> Point (float_of_int (fst e), float_of_int (snd e))) [(0, 0); (0, 1); (1, 1); (2, 1); (3, 1); (4, 1); (5, 1); (6, 1)];;
let scaling_factor = 30.0;;
mk_screen ();;
draw_room room1 scaling_factor;;
visualize room1 route scaling_factor;;
clear_screen ();;
