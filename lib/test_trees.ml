(* One can use these trees to test the Sentinel's in Graphs problem*)

let short_med_long_path =
	["14"; "0 1"; "1 2"; "2 3";
	"1 4"; "4 5"; "5 6"; "6 3";
	"1 7"; "7 8"; "8 9"; "9 10"; "10 11"; "11 12"; "12 13"; "13 3"]

let cycle_tree =
	["6"; "0 1"; "1 2"; "2 3"; "3 4"; "4 5"; "5 2"]
	
	
(*Graph from Lecture*)
	
let example_graph = 
	([|"a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"; "k"|],
	[(0, 1); (1, 2); (2, 3); (2, 4); (2, 5); (3, 4); (3, 6); (4, 7); (4, 8);
	(5, 9); (6, 3); (7, 10); (8, 3); (9, 1); (9, 2); (10, 2)])

	
	
	 
	
(* Procedure to form tree from example_graph after opening the required modules

let example_graphe = read_graph_and_payloads 11 (fst example_graph) (snd example_graph) ([] : (int * int * unit) list) 

let sentinel_of_example = sentinel_tree (0, example_graphe);;

let viz_sentinel_of_example = visualize_sentinel_tree sentinel_of_example;;

let read_sentinel_of_example = graphviz_with_payload viz_sentinel_of_example (fst example_graph) "example_graph.dot";;

 *)


	
