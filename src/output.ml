open Alschemes;;

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

(*type bexprUnDef = bexpr
                | HasModel
                | IsSat
                | IsValid
                | IsEquiv
                | Prop of string * (intTerm list)
               *)

type program = PSkip
             | PPrint of string
             (*| PITE of bexpr * program * program
             | PITEU of bexprUnDef * program * program * program*)
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
         | PPrint(s) -> print_string(s)
         | PComp(p1,p2) -> run eval solver p1; run eval solver p2
         (*
         | PITE(phi,p1,p2) -> let beval = function HasModel -> (match solver#get_solve_result with
                                                                 SolveSatisfiable -> true
                                                               | _ -> false)
                                                 | Prop(x,ts) -> let ps = List.map (evalTerm eval) ts in
                                                                 solver#get_variable_bool (x,ps)
                                                 | BAnd(phi,psi) -> (beval phi) && (beval psi)
                                                 | BOr(phi,psi) -> (beval phi) || (beval psi)
                                                 | BNeg(phi) -> not (beval phi)
                              in
                              let b = beval phi in
                              if b then
                                run eval solver p1
                              else
                                run eval solver p2
                                *)
         (*| PITE(phi, p1, p2) -> let beval = function BAnd(phi,psi) -> (beval phi) && (beval psi)
                                                    | BOr(phi,psi) -> (beval phi) || (beval psi)
                                                    | BNeg(phi) -> not beval phi
                                in let b = beval phi in
                                if b then
                                    run eval solver p1
                                else
                                    run eval solver p2

         | PITEU(phi, p1, p2, p3) -> let beval = function HasModel -> (match solver#get_solve_result with
                                                                            SolveSatisfiable -> true
                                                                            | SolveUnsatisfiable -> false
                                                                            | _ -> -1)
                                                          | IsSat -> (match solver#get_solve_result with
                                                                            SolveSatisfiable -> true
                                                                            | SolveUnsatisfiable -> false
                                                                            | _ -> -1)
                                                          | IsEquiv -> (match solver#get_solve_result with
                                                                            SolveEquiv -> true
                                                                            | SolveUnequiv -> false
                                                                            | _ -> -1)
                                                          | IsValid -> (match solver#get_solve_result with
                                                                            SolveValid -> true
                                                                            | SolveUnvalid -> true
                                                                            | _ -> -1)
                                                          | Prop(x,ts) -> let ps = List.map (evalTerm eval) ts in
                                                                          solver#get_variable_bool (x,ps)
                                                          (* todo antowoten des Sovers anpassen *)
                                     in let b = beval phi in
                                     match b with
                                        true -> run eval solver p1
                                        | false -> run eval solver p2
                                        | -1 -> run eval solver p3


        *)

         | PFor(i,s,n,t,p) -> () (* TODO! implementieren *)
