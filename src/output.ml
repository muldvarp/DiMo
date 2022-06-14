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

type bexpr = HasModel
           | BNeg of bexpr
           | BAnd of bexpr * bexpr
           | BOr of bexpr * bexpr
           | Prop of string * (intTerm list)

type program = PSkip
             | PExit
             | PPrint of string
             | PPrintf of string * string list
             | PITEU of bexpr * program * program * program
             | PFor of string * intTerm * intTerm * intTerm * program
             | PComp of program * program
             | PForEach of string * program

(* TODO:
   - FOREACH-Schleife über alle verwendeten Propositionen; dafür: Datentyp um Meta-Variablen für Propositionen erweitern!
   - Datentyp intTerm für Laufvariablen aus Alschemes einbauen
   - Designfrage: wieviel Luxus für formatierte Ausgabe soll es werden?
   - Frage: soll Ausgabe von Statistik etc. auch extra möglich sein?
 *)


let rec run params solver program =
    (*TODO*)

    (*Auxiliary functions*)
    let get_value parameters variable =
        (* Returns the value of a parameter in the parameters list.
        param:      parameters: (string, domain) list; variable: string;
        return:     the current value of the variable: int;
        *)
        let rec aux = function
            | (name, domain)::tail ->   begin
                                            if name = variable then
                                                            begin
                                                                match domain with
                                                                    | FinSet (valueList) -> (List.nth valueList 0)
                                                                    | _ -> failwith "Only the first value of a finite set can be output."
                                                            end
                                            else aux tail
                                        end
            |[] -> failwith "Variable not defined"
        in
        aux parameters in

    let add_new_parameter parameters variable startValue =
        (* Add a new parameter to the parameters list.
        params:     parameters: (string, domain) list; variable: string; startValue: int;
        return:     the parameters with the new Variable:  (string, domain) list;
        *)
        let check_is_in_variables parametersList variableName =
            let rec aux = function
                | [] -> false
                | (name, _):: tail -> if name = variableName then true else aux tail
            in
            aux parametersList
        in
        if check_is_in_variables parameters variable then failwith "Variable name already exists"
        else (variable, FinSet([startValue]))::parameters in

    let remove_from_parameters parameters variableName =
        (* Remove a parameter from the parameters list.
        params:     parameters: (string, domain) list; variableName: string;
        return:     the parameters without the variable:  (string, domain) list;
        *)
        let rec aux new_parameters = function
            | [] -> failwith "Not in List"
            | (name, domain)::tail -> if name = variableName then new_parameters@tail else aux ((name, domain)::new_parameters) tail
        in
        aux [] parameters in

    let update_parameters parameters variableName newValue =
        (* Update a parameter from the parameters list.
        params:     parameters: (string, domain) list; variableName: string; newValue: int;
        return:     the parameters with the updated variable:  (string, domain) list;
        *)
        add_new_parameter (remove_from_parameters parameters variableName) variableName newValue in

    let prog_for parameters variableName startVal stepSi stopVal subProg =
        (* For loop over a variable.
        params: parameters: (string, domain) list;
                variableName: string;
                startValue: int;
                stepSize: int;
                stopValue: int;
                subProg: programm; a program which is executed in the loop body.
        return: None;
        *)

        (*TODO get in from intTerm der Eingabevariablen*)
        let startValue = 1 in
        let stepSize = 1 in
        let stopValue = 10 in

        let rec auxForward parameters currentValue =
            (* Iterate forward and run the given subProg.
            params: parameters: (string, domain) list; the current Parameter values.
                    currentValue: int;
            return None
            *)
                if currentValue <= stopValue then begin
                    let updated_parameters = update_parameters parameters variableName currentValue;
                    in
                	subProg updated_parameters;
                	auxForward updated_parameters (currentValue + stepSize);
                end
        in

        let rec auxBackward parameters currentValue =
            (* Iterate backward and run the given subProg.
            params: parameters: (string, domain) list; the current Parameter values.
                    currentValue: int;
            return None
             *)
            if currentValue >= stopValue then begin
            	let updated_parameters = update_parameters parameters variableName currentValue;
            	in
            	subProg updated_parameters;
            	auxBackward updated_parameters (currentValue + stepSize);
            end
        in

        if stepSize = 0 then failwith "The stepSize cannot be 0.";

        (*Check if it a forward or backward iteration*)
        if stepSize > 0 then auxForward (add_new_parameter parameters variableName startValue) startValue
        else auxBackward (add_new_parameter parameters variableName startValue) startValue in

    let prog_printf_string parameters str variables =
        (* Print a formatted string and use the conventional placeholder %i for a value of a variable.
            Current!! Only you only print FinSet of domain.
        params: parameters: (string, domain) list; the current Parameter values.
                str:        string; the output string.
                variables:  (string)list; variables whose values are to be output.
        return: None
        *)
        let length = String.length str -1  in

        let rec aux currentPos variables =
            (* iterate over the string and print the char at this position or if at this position a placeholder, then print
                the current value of this
            params: currentPos: int; the current position in string.
                    variable: (string) list; list with all variables whose are to be output.
            return: None
             *)
            if (currentPos == length) && (List.length variables > 0) then failwith "to much values";

                if (currentPos <= length) then begin
                    if (currentPos < length) && ((String.get str currentPos) = '%') && ((String.get str (currentPos + 1)) = 'i') then
                        match variables with
                            | [] -> failwith "to less values"
                            | head::tail -> print_int (get_value parameters head); aux (currentPos + 1) tail;
                    else
                        begin
                            if not ((currentPos > 0) && ((String.get str (currentPos - 1)) = '%') && ((String.get str currentPos) = 'i')) then print_char (String.get str currentPos);
                            aux (currentPos + 1) variables
                        end
                end
            in
            aux 0 variables in

    let prog_if_else_undefined phi prog_if prog_else prog_undefined =
        (*TODO*)
        let rec boolean_evaluation = function
            (*TODO*)
            | BAnd(phi, psi) ->
                begin
                    let e1 = (boolean_evaluation phi) in
                    let e2 = (boolean_evaluation psi) in
                    match (e1, e2) with
                        | (_, -1)   -> -1
                        | (-1, _)   -> -1
                        | (0, 1)    -> 0
                        | (1, 0)    -> 0
                        | (0, 0)    -> 0
                        | (1, 1)    -> 1
                        | _         -> -1
                end
            | BOr(phi, psi) ->
                begin
                    let e1 = (boolean_evaluation phi) in
                    let e2 = (boolean_evaluation psi) in
                    match (e1, e2) with
                        | (_, -1)   -> -1
                        | (-1, _)   -> -1
                        | (0, 1)    -> 0
                        | (1, 0)    -> 0
                        | (0, 0)    -> 0
                        | (1, 1)    -> 1
                        | _         -> -1
                end
            | BNeg(phi) ->
                begin
                    match (boolean_evaluation phi) with
                        | -1    -> -1
                        | 1     -> 0
                        | 0     -> 1
                        | _     -> -1
                end
            | HasModel ->
                begin
                    match solver#get_solve_result with
                        | SolveSatisfiable -> 1
                        | SolveUnsatisfiable -> 0
                        | _ -> -1
                end
            | Prop (_, _) -> 0 (*TODO nur platzhalter*)
            (* TODO
            | Prop(x,ts) ->
                begin
                    let ps = List.map (evalTerm params) ts in
                    match solver#get_variable_bool (x,ps) with
                        | true -> 1
                        | false -> 0
                        | _ -> -1
                end
            *)
            in
        let evaluation = boolean_evaluation phi in
        match evaluation with
            | 1  -> run params solver prog_if
            | 0  -> run params solver prog_else
            | -1 -> run params solver prog_undefined in

    (*begin main code of the function*)
    match program with
        | PSkip                                                 -> ()
        | PExit                                                 -> failwith ""
        | PPrint(str)                                           -> print_string(str)
        | PComp(prog_1, prog_2)                                 -> run params solver prog_1; run params solver prog_2
        | PITEU(phi, prog_if, prog_else, prog_undefined)        -> prog_if_else_undefined phi prog_if prog_else prog_undefined
        | PPrintf(str, values)                                  -> prog_printf_string params str values
        | PFor(varName, startVal, stopVal, stepSize, subProg)   -> prog_for params varName startVal stepSize stopVal subProg
        | PForEach(_, _)                                        -> () (*TODO*)
;;
