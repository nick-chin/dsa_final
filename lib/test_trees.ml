let short_med_long_path =
	["14"; "0 1"; "1 2"; "2 3";
	"1 4"; "4 5"; "5 6"; "6 3";
	"1 7"; "7 8"; "8 9"; "9 10"; "10 11"; "11 12"; "12 13"; "13 3"]

let cycle_tree =
	["6"; "0 1"; "1 2"; "2 3"; "3 4"; "4 5"; "5 2"]
	
let example_graph = 
	([|"a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"; "k"|],
	[(0, 1); (1, 2); (2, 3); (2, 4); (2, 5); (3, 4); (3, 6); (4, 7); (4, 8);
	(5, 9); (6, 3); (7, 10); (8, 3); (9, 1); (9, 2); (10, 2)])
	
	
(* 	let example_graph1 = 
	([|"a"; "b"; "u"; "v"|],
	[(0, 1); (0, 2); (1, 3); (2, 3)])
	
	let example_graph2 = 
	([|"a"; "b"; "c"; "d"; "u"; "v"|],
	[(0, 1); (0, 2); (1, 3); (2, 4); (3, 5); (4, 5)])
	
	let example_graph3 = 
	([|"a"; "b"; "c";  "u"; "v"|],
	[(0, 1); (1, 2); (2, 3); (2, 4); (3, 4)])
	
	let example_graph4 = 
	([|"a"; "b"; "c";  "d"; "e"; "f"|],
	[(0, 1); (0, 2); (0, 3); (1, 4); (2, 5); (3,5); (4,5)])
	
	let example_graph5 = 
	([|"0"; "1"; "2";  "3"; "4"; "5"; "6"; "7"; "8"|],
	[(0, 1); (1, 2); (2, 3); (3, 4); (3, 5); (3,6); (4,7); (7,8); (4,8); (5,8); (6,8)])
	
	let example_graphe5 = read_graph_and_payloads 9 (fst example_graph5) (snd example_graph5) ([] : (int * int * unit) list)
	let sentinel_of_example = sentinel_tree (0, example_graphe5);;
	
	let example_graphe4 = read_graph_and_payloads 6 (fst example_graph4) (snd example_graph4) ([] : (int * int * unit) list)
	
	let example_graphe3 = read_graph_and_payloads 5 (fst example_graph3) (snd example_graph3) ([] : (int * int * unit) list)
	
	let example_graphe2 = read_graph_and_payloads 6 (fst example_graph2) (snd example_graph2) ([] : (int * int * unit) list)
	 
	let example_graphe1 = read_graph_and_payloads 4 (fst example_graph1) (snd example_graph1) ([] : (int * int * unit) list)
	 *)
	
(* let example_graphe = read_graph_and_payloads 11 (fst example_graph) (snd example_graph) ([] : (int * int * unit) list) 

let sentinel_of_example = sentinel_tree (0, example_graphe);;

let viz_sentinel_of_example = visualize_sentinel_tree sentinel_of_example;;

let read_sentinel_of_example = graphviz_with_payload viz_sentinel_of_example (fst example_graph) "sentinel.dot"

 *)


	
