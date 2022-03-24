open Alschemes;;
open Satwrapper;;

let max_col = 40
let debug_level = ref 0
	      
let output l i s = if l <= !debug_level then (print_string (String.make (2 * i) ' ' ^ s); flush stdout) else ()

let announce_and_do l i s f = if l <= !debug_level then
                                begin
                                  print_string (String.make (2 * i) ' ' ^ s ^ " " ^ String.make (max 0 (max_col - (String.length s) - 1)) '.' ^ " ");
                                  flush stdout;
                                  let result = f in
                                  print_string "done!\n";
                                  result
                                end
                              else
                                f

(*
type field = RawFormula
           | TidiedFormula
           | CNFFormula
           | ParameterEvaluation
           | PropositionalModel
           | Result
           
type output = Text of string
            | WaitFor of field
            | FillWothDots
            | LineBreak

let normaloutput = [ Text("Instance "); WaitFor ParameterEvaluation; FillWithDots; WaitFor Result; LineBreak ]
 *)

(*
type bexpr = HasModel
           | Prop of string * (intTerm list)
           | BNeg of bexpr
           | BAnd of bexpr * bexpr
           | BOr of bexpr * bexpr
*)

type bexpr = BNeg of bexpr
           | BAnd of bexpr * bexpr
           | BOr of bexpr * bexpr
           | HasModel
           | IsSat
           | IsValid
           | IsEquiv
           | Prop of string * (intTerm list)

type program = PSkip
             | PExit
             | PPrint of string
             | PPrintf of string * string
             | PITEU of bexpr * program * program * program
             | PFor of string * intTerm * intTerm * intTerm * program
             | PComp of program * program

(* TODO:
   - FOREACH-Schleife über alle verwendeten Propositionen; dafür: Datentyp um Meta-Variablen für Propositionen erweitern!
   - Datentyp intTerm für Laufvariablen aus Alschemes einbauen
   - Designfrage: wieviel Luxus für formatierte Ausgabe soll es werden?
   - Frage: soll Ausgabe von Statistik etc. auch extra möglich sein? 
 *)

                      
let rec run eval solver =
  function PSkip -> ()
         | PExit -> () (*TODO programm ab hier nicht mehr ausführen      exception schmeißen außerhalb abfangen*)
         | PPrint(s) -> print_string(s)
         | PPrintf(s, var) -> ()(*TODO ausgeben der aktuellen Variablen werte       *)
         | PComp(p1,p2) -> run eval solver p1; run eval solver p2
         | PITEU(phi, p1, p2, p3) -> begin
                                        let rec beval = function
                                        (* todo antowoten des Solvers anpassen *)
                                        | BAnd(phi, psi) -> begin
                                                                let e1 = (beval phi) in
                                                                let e2 = (beval psi) in
                                                                match (e1, e2) with
                                                                    | (0, _) -> 0
                                                                    | (_, 0) -> 0
                                                                    | (1, 1) -> 1
                                                                    | (1, -1) -> -1
                                                                    | (-1, 1) -> -1
                                                                    | (-1, -1) -> -1
                                                                    | _ -> -1
                                                            end

                                        | BOr(phi, psi) ->  begin
                                                                let e1 = (beval phi) in
                                                                let e2 = (beval psi) in
                                                                match (e1, e2) with
                                                                    | (1, _) -> 1
                                                                    | (_, 1) -> 1
                                                                    | (0, 0) -> 0
                                                                    | (0, -1) -> -1
                                                                    | (-1, 0) -> -1
                                                                    | (-1, -1) -> -1
                                                                    | _ -> -1
                                                            end

                                        | BNeg(phi) ->  begin
                                                            match beval phi with
                                                                | -1 -> -1
                                                                | 1 -> 0
                                                                | 0 -> 1
                                                                | _ -> -1
                                                        end

                                        | HasModel ->   begin
                                                            match solver#get_solve_result with
                                                                | SolveSatisfiable -> 1
                                                                | SolveUnsatisfiable -> 0
                                                                | _ -> -1
                                                        end

                                        | IsSat ->      begin
                                                            match solver#get_solve_result with
                                                                | SolveSatisfiable -> 1
                                                                | SolveUnsatisfiable -> 0
                                                                | _ -> -1
                                                        end

                                        | IsEquiv ->    begin
                                                            match solver#get_solve_result with
                                                                | SolveSatisfiable -> 1
                                                                | SolveUnsatisfiable -> 0
                                                                | _ -> -1
                                                        end

                                       | IsValid ->     begin
                                                            match solver#get_solve_result with
                                                                | SolveSatisfiable -> 1
                                                                | SolveUnsatisfiable -> 0
                                                                | _ -> -1
                                                        end


                                       | Prop(x,ts) ->  begin
                                                            let ps = List.map (evalTerm eval) ts in
                                                            match solver#get_variable_bool (x,ps) with
                                                                | true -> 1
                                                                | false -> 0
                                                                | _ -> -1
                                                        end

                                     in
                                     let b = beval phi
                                     in
                                     match b with
                                        | 1 -> run eval solver p1   (*true*)
                                        | 0 -> run eval solver p2   (*false*)
                                        | _ -> run eval solver p3   (*undefined*)
                                end

         | PFor(i,s,n,t,p) -> () (* TODO! implementieren *)
