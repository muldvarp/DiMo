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
             | PPrintf of string * (string list)
             | PITEU of bexpr * program * program * program
             | PFor of string * intTerm * intTerm * intTerm * program
             | PComp of program * program
             | PForEach

(* TODO:
   - FOREACH-Schleife über alle verwendeten Propositionen; dafür: Datentyp um Meta-Variablen für Propositionen erweitern!
   - Datentyp intTerm für Laufvariablen aus Alschemes einbauen
   - Designfrage: wieviel Luxus für formatierte Ausgabe soll es werden?
   - Frage: soll Ausgabe von Statistik etc. auch extra möglich sein?
 *)


let rec run variables eval solver program =
    (*Todo eval und variables zusammenführen*)
    let add_to_variables list var value =
        let check_is_in_variables l varName =
            let rec aux = function
                | [] -> false
                | Counter (h, _):: t -> if h = varName then true else aux t
            in
            aux l
        in
        if check_is_in_variables list var then failwith "Variable name already exists"
        else Counter (var, value)::list
    in

    let remove_from_variables list varName =
        let rec aux l = function
            | [] -> failwith "Not in List"
            | Counter (h, v)::t -> if h = varName then l@t else aux ( Counter (h, v)::l) t
        in
        aux [] list
    in

    let update_variables list varName value = add_to_variables (remove_from_variables list varName) varName value
    in

    let intTermToInt = function
                        | Const c -> c
                        | Counter (_, v) -> v
                        (*TODO andere Fälle mit einbeziehen*)
                        | _ -> failwith "Cannot get the value of the intTerm"
    in

    match program with
        | PSkip -> ()
        | PExit -> () (*TODO programm ab hier nicht mehr ausführen      exception schmeißen außerhalb abfangen*)
        | PPrint(s) -> print_string(s)
        | PPrintf(str, values) -> begin
                                    let length = String.length str -1  in

                                    let rec get_value var = function
                                            | [] -> failwith "Variable not defined"
                                            | Counter (varName, value)::t ->  begin
                                                                                if varName = var then value
                                                                                else get_value var t
                                                                              end in

                                    let rec aux i values =
                                            if (i == length) && (List.length values > 0) then failwith "to much values";

                                            if (i <= length) then begin
                                                if (i < length) && ((String.get str i) = '%') && ((String.get str (i + 1)) = 'i') then
                                                    match values with
                                                        | [] -> failwith "to less values"
                                                        | h::t -> print_int (get_value h variables); aux (i + 1) t;
                                                else
                                                    begin
                                                        if not ((i > 0) && ((String.get str (i - 1)) = '%') && ((String.get str i) = 'i')) then print_char (String.get str i);
                                                        aux (i + 1) values
                                                    end
                                            end
                                    in
                                    aux 0 values
                                  end
        | PComp(p1,p2) -> run variables eval solver p1; run variables eval solver p2
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
                                        | 1 -> run variables eval solver p1   (*true*)
                                        | 0 -> run variables eval solver p2   (*false*)
                                        | -1 -> run variables eval solver p3   (*undefined*)
                                end

         | PFor(varName, start, stop, step, pr) ->  begin
                                                        let startValue = intTermToInt start in
                                                        let stopValue = intTermToInt stop in
                                                        let stepValue = intTermToInt step in

                                                        let rec aux variables value =
                                                            if value <= stopValue then begin
                                                                let updated_variables = update_variables variables varName value;
                                                                in
                                                                aux updated_variables (value + stepValue);
                                                                run updated_variables eval solver pr;
                                                            end
                                                        in
                                                        aux (add_to_variables variables varName startValue) startValue
                                                    end
         | PForEach -> ()