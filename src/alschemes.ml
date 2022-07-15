open Enumerators ;;
open PropFormula ;;

module IntSet = Set.Make(struct
                    type t = int
                    let compare = compare
                  end);;


type intTerm = Const of int
             | Param of string
             | BinOp of string * intTerm * intTerm * (int -> int -> int)
             | UnOp of string * intTerm * (int -> int)
             | SetOp of string * symbSet * (IntSet.t -> int)

and symbSet = SmallSet of intTerm list
            | Enumeration of intTerm * intTerm * intTerm
            | BinSetOp of string * symbSet * symbSet * (IntSet.t -> IntSet.t -> IntSet.t)
(*             | Union of symbSet * symbSet
             | Isect of symbSet * symbSet
             | Diff of symbSet * symbSet *)


(*TODO hier weg und zyklische abhängigkeit auflösen*)
type bexpr = HasModel
           | BNeg of bexpr
           | BAnd of bexpr * bexpr
           | BOr of bexpr * bexpr
           | Prop of string * (intTerm list)
           | BComp of intTerm * (int -> int -> bool) * intTerm

type outprog = PSkip
             | PExit
             | PPrint of string
             | PPrintf of string * intTerm list
             | PITEU of bexpr * outprog * outprog * outprog
             | PFor of string * intTerm * intTerm * intTerm * outprog
             | PComp of outprog * outprog
             | PForEach of string * outprog

let rec compareIntTerm =
  let order = function Const _ -> 0
                     | Param _ -> 1
                     | UnOp _  -> 2
                     | BinOp _ -> 3
                     | SetOp _ -> 4
  in
  let rec comp t t' =
    let c = (order t) - (order t') in
    if c < 0 then -1 else
      if c > 0 then 1 else
        match (t,t') with
          (Const c, Const c') -> compare c c'
        | (Param p, Param p') -> compare p p'
        | (UnOp(s,t,_),UnOp(s',t',_)) -> let c = compare s s' in
                                         if c<>0 then c else comp t t'
        | (BinOp(s,t1,t2,_),BinOp(s',t1',t2',_)) -> let c = compare s s' in
                                                    if c<>0 then c else
                                                      let c = comp t1 t1' in
                                                      if c<>0 then c else comp t2 t2'
        | (SetOp(s,m,_),SetOp(s',m',_)) -> let c = compare s s' in
                                           if c<>0 then c else compareSymbSet m m'
        | _ -> failwith "compareIntTerm: cannot handle two different arguments!"
  in
  comp
and compareSymbSet =
  let order = function SmallSet _    -> 0
                     | Enumeration _ -> 1
                     | BinSetOp _    -> 2
  in
  let rec comp m m' =
    let c = (order m) - (order m') in
    if c < 0 then -1 else
      if c > 0 then 1 else
        match (m,m') with
          (SmallSet es, SmallSet es') -> let l = (List.length es) - (List.length es') in
                                         if l<0 then -1 else if l>0 then 1 else
                                           List.fold_left2 (fun d -> fun t -> fun t' -> if d<>0 then d else compareIntTerm t t') 0 es es' 
        | (Enumeration(t1,t2,t3),Enumeration(t1',t2',t3')) -> let c1 = compareIntTerm t1 t2 in
                                                              if c1<>0 then c1 else let c2 = compareIntTerm t2 t2' in
                                                                                    if c2<>0 then c2 else compareIntTerm t3 t3'
        | (BinSetOp(s,m1,m2,_),BinSetOp(s',m1',m2',_)) -> let c = compare s s' in
                                                          if c<>0 then c else
                                                            let c = comp m1 m1' in
                                                            if c<>0 then c else comp m2 m2'
        | _ -> failwith "compareSymbSet: cannot handle two different arguments!"
  in
  comp
  
type alScheme = STrue
	      | SFalse
	      | SPred of string * (intTerm list)
              (* | SAbbr of string * (intTerm list) *)
              | SNeg of alScheme
              | SAnd of alScheme * alScheme
              | SOr of alScheme * alScheme
              | SImp of alScheme * alScheme
              | SBiimp of alScheme * alScheme
              | SForall of string * symbSet * alScheme
              | SForsome of string * symbSet * alScheme


module StringSet = Set.Make(String) ;;

type propositions = StringSet.t 
type constraints = (string * (int -> int -> bool) * string) list
               
type domain = From of int * int
            | FromTo of int * int * int
	        | FinSet of int list

type parameters = (string * domain) list
(* type scheme = string * (string list) *)
type definitions = (string * (intTerm list) * alScheme) list
              
type problem = ProblemSat of propositions * parameters * constraints * alScheme * definitions * outprog
             | ProblemVal of propositions * parameters * constraints * alScheme * definitions * outprog
             | ProblemEquiv of propositions * parameters * constraints * alScheme * alScheme * definitions
             | ProblemModels of propositions * parameters * constraints * alScheme * definitions * outprog
(*             | ProblemGenEquiv of propositions * parameters * constraints * alScheme * alScheme * definitions *)


let makeEnumerator =
  let mkOne x = function From(s,t)     -> new natEnumerator x s t None
                       | FromTo(s,t,z) -> new natEnumerator x s t (Some z)
		       | FinSet(es)    -> new finiteSetEnumerator x es
  in
  let rec mkEnum = function []        -> new emptyEnumerator
                          | [(x,d)]   -> mkOne x d 
                          | (x,d)::ds -> let e = mkOne x d in
                                         let e' = mkEnum ds in
                                         new pairEnumerator e e'
  in
  mkEnum

             
let rec remove_dups = function []    -> []
                             | x::xs -> x::(remove_dups (List.filter (fun y -> y != x) xs))
  
let showScheme =
  let rec showTerm = function Const(i)    -> string_of_int i
                            | Param(x)    -> x
                            | UnOp(s,t,_) -> let (lparen,rparen) = match t with BinOp(_,_,_,_) -> ("(",")")
                                                                              | _              -> ("","")
                                             in
                                             s ^ lparen ^ showTerm t ^ rparen     
                            | BinOp(s,t,t',_) -> let (lparen,rparen) = match t with BinOp(_,_,_,_) -> ("(",")")
                                                                                  | _              -> ("","")
                                                 in
                                                 let (lparen',rparen') = match t' with BinOp(_,_,_,_) -> ("(",")")
                                                                                     | _              -> ("","") 
                                                 in
                                                 lparen ^ showTerm t ^ rparen ^ s  ^ lparen' ^ showTerm t' ^ rparen' 
                            | SetOp(s,m,_) -> s ^ " " ^ showSet m 
  and showSet = function SmallSet(tl)       -> "{" ^ String.concat "," (List.map showTerm (remove_dups (List.sort compareIntTerm tl))) ^ "}"
                       | Enumeration(f,s,l) -> let onlytwo = (match s with
                                                                BinOp("+",f',Const(1),_) -> 0 = compareIntTerm f f'
                                                              | _                        -> false)
                                               in
                                               "{" ^ showTerm f ^ "," ^ (if not onlytwo then (showTerm s ^ ",") else "") ^ "..," ^ showTerm l ^ "}"
                       | BinSetOp(s,m,m',_) -> let (lparen,rparen) = match m with BinSetOp _ -> ("(",")")
                                                                                | _          -> ("","")
                                               in
                                               let (lparen',rparen') = match m' with BinSetOp _ -> ("(",")")
                                                                                   | _          -> ("","")
                                               in
                                               lparen ^ showSet m ^ rparen ^ " " ^ s ^ " " ^ lparen' ^ showSet m' ^ rparen'
  in
  let rec show = function STrue              -> "True"
			| SFalse             -> "False"
                        | SPred(n,ps)        -> n ^ (if List.length ps > 0 then
                                                       "(" ^ String.concat "," (List.map showTerm ps) ^ ")"
                                                     else
                                                       "")
                        | SNeg(sphi)         -> let (lparen,rparen) = match sphi with
                                                                            SNeg(_)         -> ("","")
                                                                          | SPred(_)        -> ("","")
                                                                          | SForall(_,_,_)  -> ("","")
                                                                          | SForsome(_,_,_) -> ("","")
                                                                          | _               -> ("(",")")
                                                in
                                                "-" ^ lparen ^ show sphi ^ rparen
                        | SAnd(sphi,spsi)    -> let (lparen,rparen) = match sphi with
                                                                            SOr(_,_)        -> ("(",")")
                                                                          | SImp(_,_)       -> ("(",")")
                                                                          | SBiimp(_,_)     -> ("(",")")
                                                                          | SForall(_,_,_)  -> ("(",")")
                                                                          | SForsome(_,_,_) -> ("(",")")
                                                                          | _               -> ("","")
                                                in
                                                let (lparen',rparen') = match spsi with
                                                                            SOr(_,_)        -> ("(",")")
                                                                          | SImp(_,_)       -> ("(",")")
                                                                          | SBiimp(_,_)     -> ("(",")")
                                                                          | _               -> ("","")
                                                in
                                                lparen ^ show sphi ^ rparen ^ " & " ^ lparen' ^ show spsi ^ rparen'
                        | SOr(sphi,spsi)     -> let (lparen,rparen) = match sphi with
                                                                            SImp(_,_)       -> ("(",")")
                                                                          | SBiimp(_,_)     -> ("(",")")
                                                                          | SForall(_,_,_)  -> ("(",")")
                                                                          | SForsome(_,_,_) -> ("(",")")
                                                                          | _               -> ("","")
                                                in
                                                let (lparen',rparen') = match spsi with
                                                                            SImp(_,_)       -> ("(",")")
                                                                          | SBiimp(_,_)     -> ("(",")")
                                                                          | _               -> ("","")
                                                in
                                                lparen ^ show sphi ^ rparen ^ " | " ^ lparen' ^ show spsi ^ rparen'
                        | SImp(sphi,spsi)    -> let (lparen,rparen) = match sphi with
                                                                            SBiimp(_,_)     -> ("(",")")
                                                                          | SForall(_,_,_)  -> ("(",")")
                                                                          | SForsome(_,_,_) -> ("(",")")
                                                                          | _               -> ("","")
                                                in
                                                let (lparen',rparen') = match spsi with
                                                                            SBiimp(_,_)     -> ("(",")")
                                                                          | _               -> ("","")
                                                in
                                                lparen ^ show sphi ^ rparen ^ " -> " ^ lparen' ^ show spsi ^ rparen'
                        | SBiimp(sphi,spsi)  -> let (lparen,rparen) = match sphi with
                                                                            SBiimp(_,_)     -> ("(",")")
                                                                          | SForall(_,_,_)  -> ("(",")")
                                                                          | SForsome(_,_,_) -> ("(",")")
                                                                          | _               -> ("","")
                                                in
                                                let (lparen',rparen') = match spsi with
                                                                            SBiimp(_,_)     -> ("(",")")
                                                                          | _               -> ("","")
                                                in
                                                lparen ^ show sphi ^ rparen ^ " <-> " ^ lparen' ^ show spsi ^ rparen'
                        | SForall(x,m,sphi)  -> "FORALL " ^ x ^ " in " ^ showSet m ^ ". " ^ show sphi
                        | SForsome(x,m,sphi) -> "FORSOME " ^ x ^ " in " ^ showSet m ^ ". " ^ show sphi
  in
  show
    

let rec evalTerm eval = function Const(i)        -> i
                               | Param(x)        -> (try
                                                       match ParamEval.find x eval with
						         Int v -> v
                                                                    (* | _     -> failwith ("Parameter `" ^ x ^ "´ has wrong type!") *)
                                                     with Not_found -> failwith ("Undefined parameter `" ^ x ^ "'"))
                               | BinOp(_,t,t',f) -> f (evalTerm eval t) (evalTerm eval t')
                               | UnOp(_,t,f)     -> f (evalTerm eval t)
                               | SetOp(_,m,f)    -> f (evalSet eval m)
and evalSet eval = function SmallSet(tl)          -> IntSet.of_list (List.map (evalTerm eval) tl)
                          | Enumeration(t,t',t'') -> let first = evalTerm eval t in
                                                     let second = evalTerm eval t' in
                                                     let last = evalTerm eval t'' in
                                                     let step = second-first in
                                                     if last < first then
                                                       IntSet.empty
                                                     else if step <= 0 then
                                                       failwith ("Illegal definition of enumeration set: {" ^ string_of_int first ^
                                                                   (if step <> 1 then "," ^ string_of_int second else "") ^ ",..," ^ string_of_int last ^ "}")
                                                     else 
                                                       let rec makeSet m f = if f <= last then makeSet (IntSet.add f m) (f+step) else m in
                                                       makeSet IntSet.empty first
                          | BinSetOp(_,m1,m2,f)   -> f (evalSet eval m1) (evalSet eval m2)                                                        
                                                   
let instantiate sphi defs eval =
  let rec instScheme pos eval =
    function STrue              -> if pos then And [] else Or []
	   | SFalse             -> if pos then Or [] else And []
           | SPred(n,ps)        -> let values = List.map (evalTerm eval) ps in
                                   let rec find_def =
				     function []           -> None
                                            | (m,ps,f)::ds -> if n <> m || List.length values <> List.length ps then
								find_def ds
                                                              else
                                                                begin
                                                                  let vps = List.combine ps values in
                                                                  let rec buildEval acc =
								    function []                 -> Some (f,acc)
                                                                           | ((Param(p),v)::xs) -> buildEval (ParamEval.add p (Int(v)) acc) xs
                                                                           | ((Const(c),v)::xs) -> if c=v then buildEval acc xs else find_def ds
                                                                  in
                                                                  buildEval ParamEval.empty vps
                                                                end
                                   in
				   begin
				     match find_def defs with
				       None              -> Lit(pos,n,values)
				     | Some (sphi,eval') -> instScheme pos eval' sphi
				   end
           | SNeg(sphi)         -> instScheme (not pos) eval sphi 
           | SAnd(sphi,spsi)    -> if pos then
                                     And [instScheme true eval sphi; instScheme true eval spsi]
                                   else
                                     Or [instScheme false eval sphi; instScheme false eval spsi]
           | SOr(sphi,spsi)     -> if pos then
                                     Or [instScheme true eval sphi; instScheme true eval spsi]
                                   else
                                     And [instScheme false eval sphi; instScheme false eval spsi]
           | SImp(sphi,spsi)    -> if pos then
                                     Or [instScheme false eval sphi; instScheme true eval spsi]
                                   else
                                     And [instScheme true eval sphi; instScheme false eval spsi]
           | SBiimp(sphi,spsi)  -> if pos then
                                     Biimp(instScheme true eval sphi, instScheme true eval spsi)
                                   else
                                     Biimp(instScheme false eval sphi, instScheme true eval spsi)
           | SForall(x,s,sphi)  -> if pos then
                                     And (List.map (fun v -> instScheme true (ParamEval.add x (Int(v)) eval) sphi) (IntSet.elements (evalSet eval s)))
                                   else
                                     Or (List.map (fun v -> instScheme false (ParamEval.add x (Int(v)) eval) sphi) (IntSet.elements (evalSet eval s)))
           | SForsome(x,s,sphi) -> if pos then
                                     Or (List.map (fun v -> instScheme true (ParamEval.add x (Int(v)) eval) sphi) (IntSet.elements (evalSet eval s)))
                                   else
                                     And (List.map (fun v -> instScheme false (ParamEval.add x (Int(v)) eval) sphi) (IntSet.elements (evalSet eval s)))
  in
  instScheme true eval sphi



(*TODO ab hier weg... *)


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
                            | head::tail -> print_int (intTerm_to_int parameters head); aux (currentPos + 1) tail;
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
                        | (0, 1)    -> 1
                        | (1, 0)    -> 1
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
                (*TODO bei zugriff außerhalb des Bereichs wertet sich ausdruck nicht zu -1 aus*)
                begin
                    let ps = List.map (intTerm_to_int params) ts in
                    match solver#get_variable_bool (x,ps) with
                        | true -> 1
                        | false -> 0
                        | _ -> -1
                end
            | BComp(term1, compOper, term2) ->
                begin
                    let cmpRes = compOper (intTerm_to_int params term1) (intTerm_to_int params term2) in
                    if cmpRes then 1 else 0
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
        | PPrint(str)                                           -> output 0 0 (String.sub str 1 ((String.length str) - 2))
        | PComp(prog_1, prog_2)                                 -> run_output_language params solver prog_1;
                                                                   run_output_language params solver prog_2
        | PITEU(phi, prog_if, prog_else, prog_undefined)        -> prog_if_else_undefined phi prog_if prog_else prog_undefined
        | PPrintf(str, values)                                  -> prog_printf_string params (String.sub str 1 ((String.length str) - 2)) values
        | PFor(varName, startVal, stopVal, stepSize, subProg)   -> prog_for params varName startVal stepSize stopVal subProg
        | PForEach(varName, subProg)                            -> prog_for_each varName subProg
;;
