open Century_problem

let%test "Century problem" =
  test_century_candidates ();
  true
  
open Sentinels_in_graphs

let%test "Sentinels-in-graphs" =
  final_test ()
