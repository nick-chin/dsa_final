open Century_problem

let%test "Century problem" =
  test_century_candidates ();
  true
  
open Sentinels_in_graphs

let%test "Sentinels-in-graphs-from-rooted-graphs" =
  final_test ()

open Watchman_problem

let%test "Watchman problem random rooms" = 
  test_random_rooms ()