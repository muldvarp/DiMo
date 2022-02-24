(* todo sollte eigentlich nicht mehr benötigt werden*)
let debug_level = ref 0
	      
let output l i s = if l <= !debug_level then (print_string (String.make (2 * i) ' ' ^ s); flush stdout) else ()

(* 0 = show all literals, 1 = show positives only, -1 = show negatives only *)                           
let visible_literals = ref 0
