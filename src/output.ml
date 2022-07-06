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

type outprog = PSkip
             | PExit
             | PPrint of string
             | PPrintf of string * string list
             | PITEU of bexpr * outprog * outprog * outprog
             | PFor of string * intTerm * intTerm * intTerm * outprog
             | PComp of outprog * outprog
             | PForEach of string * outprog

let rec run_output_language params solver program =
    (* recursive execution of the output language
    params: params: (string, domain) list; the parameter values.
            solver: solver; the solver of the formulas, not of the output.
            program: outprog; output language programm.
    return: None;
    *)

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

    let intTerm_to_int parameters term =
        (* Evaluates an intTerm.
        params: parameters: (string, domain) list; variable: string; startValue: int;
                term: intTerm; the term that we want to evaluate.
        return: int; the result of the evaluation.
        *)
        let rec aux = function
            (* Auxiliary functions to recursively evaluate sub terms of the term.
            params: sub term: intTerm;
            return: int; the result of the evaluation on this sub term.
            *)
            | Const integer                     -> integer
            | Param variable                    -> get_value parameters variable
            | BinOp(_, term_1, term_2, func)    -> func (aux term_1) (aux term_2)
            | UnOp(_, term, func)               -> func (aux term)
            | SetOp (_, set, func)              -> func (aux_set set)

        and aux_set = function
            (* Auxiliary function to recursively evaluate of a sub term as a symbSet
            params: sub term: symbSet;
            return: IntSet.t -> int; the result of the evaluation on this sub term.
            *)
            | SmallSet(termList)                -> IntSet.of_list (List.map (aux) termList)
            | BinSetOp (_, set1, set2, func)    -> func (aux_set set1) (aux_set set2)
            | Enumeration(term1, term2, term3)  -> aux_create_enumeration_set term1 term2 term3

        and aux_create_enumeration_set firstTerm secondTerm lastTerm =
            (* Auxiliary function to crate a IntSet.t of a enumeration.
            params: firstTerm: intTerm;
                    secondTerm: intTerm;
                    lastTerm: intTerm;
            return: IntSet.t; the crated set.
            *)
            let firstValue  = aux firstTerm in
            let secondValue = aux secondTerm in
            let lastValue   = aux lastTerm in
            let stepSize    = secondValue - firstValue in

            let rec makeSet m f =
                (* Recursively auxiliary function to iterate over all values between the start and the last value
                 and the value to the result set.*)
                if f <= lastValue then makeSet (IntSet.add f m) (f+stepSize)
                else m in

            (*Check if is a correct Enumeration*)
            if lastValue < firstValue then
                IntSet.empty
            else if stepSize <= 0 then
                failwith ("Illegal definition of enumeration set: {" ^ string_of_int firstValue ^
                (if stepSize <> 1 then "," ^ string_of_int secondValue else "") ^ ",..," ^string_of_int lastValue ^ "}")
            else
            (*crate a enumeration set*)
            makeSet IntSet.empty firstValue in
        (*end auxiliary functions for intTerm_to_int*)

        aux term in

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
                subProg: outprog; a program which is executed in the loop body.
        return: None;
        *)

        (* *)
        let startValue = intTerm_to_int parameters startVal in
        let stepSize = intTerm_to_int parameters stepSi in
        let stopValue = intTerm_to_int parameters stopVal in

        let rec auxForward parameters currentValue =
            (* Iterate forward and run the given subProg.
            params: parameters: (string, domain) list; the current Parameter values.
                    currentValue: int;
            return None
            *)
                if currentValue <= stopValue then begin
                    let updated_parameters = update_parameters parameters variableName currentValue;
                    in
                	run_output_language updated_parameters solver subProg;
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
            	run_output_language updated_parameters solver subProg;
            	auxBackward updated_parameters (currentValue + stepSize);
            end
        in

        if stepSize = 0 then failwith "The stepSize cannot be 0.";

        (*Check if it a forward or backward iteration*)
        if stepSize > 0 then auxForward (add_new_parameter parameters variableName startValue) startValue
        else auxBackward (add_new_parameter parameters variableName startValue) startValue in

    let prog_for_each variableName subProg =
        (*TODO*)
        () in

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
        (* A normal if else branching function with a extra undefined case for the case that the expression cannot be evaluated
        params: phi: bexpr; Expression whose evaluation determines the branch.
                prog_if: outprog; Programm of the if branch.
                prog_else: outprog; Programm of the else branch.
                prog_undefined: outprog; Programm of the undefined branch.
        return: None;
        *)
        let rec boolean_evaluation = function
            (* Recursively auxiliary function to evaluate the expression.
            params: bexpr: Expression to evaluate
            return: boolean: The evaluation of the expression.
            *)
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
            | Prop(x,ts) ->
                (*TODO bin mir nicht ganz sicher ob, wenn auf außerhalb des Definition bereichs zugegriffen wird ob
                sich ausdruck zu -1 auswertet oder ob Programm dann mit Fehler beendet wird*)
                begin
                    let ps = List.map (intTerm_to_int params) ts in
                    match solver#get_variable_bool (x,ps) with
                        | true -> 1
                        | false -> 0
                        | _ -> -1
                end

            in
        let evaluation = boolean_evaluation phi in
        match evaluation with
            | 1  -> run_output_language params solver prog_if
            | 0  -> run_output_language params solver prog_else
            | -1 -> run_output_language params solver prog_undefined
            | _  -> failwith "Error by the evaluation of the boolean expression" in

    (*begin main code of the run_output_language function*)
    match program with
        | PSkip                                                 -> ()
        | PExit                                                 -> failwith "Exit of the output programm."
        | PPrint(str)                                           -> print_string(str)
        | PComp(prog_1, prog_2)                                 -> run_output_language params solver prog_1;
                                                                   run_output_language params solver prog_2
        | PITEU(phi, prog_if, prog_else, prog_undefined)        -> prog_if_else_undefined phi prog_if prog_else prog_undefined
        | PPrintf(str, values)                                  -> prog_printf_string params str values
        | PFor(varName, startVal, stopVal, stepSize, subProg)   -> prog_for params varName startVal stepSize stopVal subProg
        | PForEach(varName, subProg)                            -> prog_for_each varName subProg
;;
