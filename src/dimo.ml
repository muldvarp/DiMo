open Alschemes ;;
open PropFormula;;
open Enumerators;;
open Engine ;;
open Arg;;
open Basics;;

module CommandLine =
struct

  let first = ref true
  let in_file = ref ""
  let in_channel = ref stdin
		    
  let list_format formatter = function [] -> "[]"
                                     | (h::t) -> (List.fold_left (fun s i -> s ^ ", " ^ (formatter i)) ("[" ^ (formatter h)) t) ^ "]";;

  let satsolv = Satsolvers.get_list ()

  let speclist =  [("--solver", String (fun s -> Satsolvers.set_default s),
                    "\n     select sat solver; " ^ if satsolv = [] then "no sat solvers included!" else (
			                             "default is " ^ ((Satsolvers.get_default ())#identifier) ^
	                                               "\n     available: " ^ list_format (fun f -> f#identifier) (Satsolvers.get_list ())));
                   ("--debug", Unit (fun _ -> debug_level := 2),
                    "\n     enable output for debugging");
                   ("--onlypos", Unit (fun _ -> visible_literals := 1),
                    "\n     show only positive literals in propositional models");
                   ("--onlyneg", Unit (fun _ -> visible_literals := -1),
                    "\n     show only negative literals in propositional models");
		   ("--timeout", Int (fun t -> timeout := float_of_int t),
		    "\n     set the timeout in seconds, default is 15")
                  ]

  let anonfun s = if !first then (in_file := s; first := false) else ()
                
  let header = "DiMo (Discrete Modelling) " ^ Version.version ^ "\nAuthor: Martin Lange, 2019\nChecks families of propositional formulas for satisfiability/validity/equivalence.\n\n"

  let usage = (header ^ "Usage: dimo [<options>] [<file>] \n\nIf <file> is ommitted then input is read from STDIN. Options are")
end ;;

open CommandLine ;;


let _ = output 1 0 "Parsing arguments ..................................... ";
        Arg.parse speclist anonfun usage;
        output 1 0 "done.\n";

        output 1 0 ("Opening input file `" ^ !in_file ^ "´ " ^ String.make (max 0 (33 - (String.length !in_file))) '.' ^ " ");
        let problem = in_channel := open_in !in_file;
                      let lexbuf = Lexing.from_channel !in_channel in
                      try
                        Parser.start Lexer.token lexbuf
                      with exn ->
                            begin
                              let curr = lexbuf.Lexing.lex_curr_p in
                              let line = curr.Lexing.pos_lnum in
                              let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
                              let tok = Lexing.lexeme lexbuf in
                              (*                              let tail = Sql_lexer.ruleTail "" lexbuf in *)
                              failwith ("Parsing error in line " ^ string_of_int line ^ ", position " ^ string_of_int cnum ^ " at token `" ^ tok ^ "'")
                            end
        in
        output 1 0 "done.\n";

        output 1 0 "Constructing engine for formula scheme .....\n";
        let engine = match problem with
            ProblemSat(props, params, constrs, sphi, defs, outProg)         ->
             output 1 1 (showScheme sphi ^ "\n");
             let report =
               fun eval ->
               fun b ->
               fun lits -> let vs = showEval eval in
                           "Instance " ^ vs ^ " " ^ String.make (max 0 (38 - (String.length vs))) '.' ^ " " ^
                             (if b then "" else "un") ^ "satisfiable." ^
                               (if b then "\n  Satisfying assignment: " ^ showModel lits else "")
             in
             new simpleSatEngine props params constrs sphi defs report outProg
          | ProblemVal(props, params, constrs, sphi, defs, outProg)         ->
             output 1 1 (showScheme sphi ^ "\n");
             let report =
               fun eval ->
               fun b ->
               fun lits -> let vs = showEval eval in
                           "Instance " ^ vs ^ " " ^ String.make (max 0 (38 - (String.length vs))) '.' ^ " " ^
                             (if not b then "" else "in") ^ "valid." ^
                               (if b then "\n  Refuting assignment: " ^ showModel lits else "")
             in
             new simpleSatEngine props params constrs (SNeg sphi) defs report outProg
          | ProblemEquiv(props, params, constrs, sphi, spsi, defs) ->
             output 1 1 ("#1: " ^ showScheme sphi ^ "\n");
             output 1 1 ("#2: " ^ showScheme spsi ^ "\n");
             let esound = new simplePi2Engine props params constrs sphi spsi defs
                            (fun b -> fun eval -> fun lits ->
                                         let vs = showEval eval in
                                         "Instance " ^ vs ^ " " ^ String.make (max 0 (38 - (String.length vs))) '.' ^ " " ^ (if not b then "un" else "") ^ "sound." ^
                                           (if not b then "\n  A model of the first but not the second formula is: " ^ showModel lits else ""))
             in
             let ecomplete = new simplePi2Engine props params constrs spsi sphi defs
                               (fun b -> fun eval -> fun lits ->
                                            let vs = showEval eval in
                                            "Instance " ^ vs ^ " " ^ String.make (max 0 (38 - (String.length vs))) '.' ^ " " ^ (if not b then "in" else "") ^ "complete." ^
                                              (if not b then "\n  A model of the second but not the first formula is: " ^ showModel lits else ""))
             in
             new combinedEngine [| esound; ecomplete |]
          | ProblemModels(props, params, constrs, sphi, defs, outProg) ->
             output 1 1 (showScheme sphi ^ "\n");
             let initreport = fun eval -> let vs = showEval eval in
                                          "Instance " ^ vs ^ " " ^ String.make (max 0 (38 - (String.length vs))) '.' ^ " "
             in
             let eachreport = fun b -> fun lits -> fun n -> if not b then (string_of_int n ^ " model" ^ (if n<>1 then "s" else "") ^ " found.")
                                                            else "  Found model " ^ showModel lits 
             in
             new modelsEngine props params constrs sphi defs initreport eachreport outProg
        in
        output 1 0 "Running engine .................................\n";
        engine#run;




                                                                       
