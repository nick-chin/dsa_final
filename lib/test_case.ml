open Century_problem

let%test "Century problem" =
  test_century_candidates ();
  true
  
open Sentinels_in_Graphs


let%test "Sentinels-in-Graphs" =
   final_test ();
  true
