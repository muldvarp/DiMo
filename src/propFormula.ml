open Basics ;;

type propFormula = True
                 | False
                 | Lit of bool * string * (int list)
                 | And of propFormula list
                 | Or of propFormula list
                 | Biimp of propFormula * propFormula


let showFormula =
  let rec show = function True -> "True"
                        | False -> "False"
                        | Lit(b,n,ps) ->
                           let pref = if not b then "-" else "" in
                           let (lparen,rparen) = if List.length ps > 0 then ("(",")") else ("","") in
                           pref ^ n ^ lparen ^ String.concat "," (List.map string_of_int ps) ^ rparen
                        | And psis ->
                           begin
                             match psis with
                               []    -> "tt"
                             (*                             | [phi] -> show phi *)
                             | _     -> String.concat " & " (List.map (fun psi -> let (lparen,rparen) = match psi with
                                                                                      Or (_::_::_) -> ("(",")")
                                                                                    | Biimp(_,_)   -> ("(",")")
                                                                                    | _            -> ("","")
                                                                                  in
                                                                                  lparen ^ show psi ^ rparen
                                                           ) psis)
                           end
                        | Or psis ->
                           begin
                             match psis with
                               []    -> "ff"
                             (*                             | [psi] -> show psi *)
                             | _     -> String.concat " | " (List.map (fun psi -> let (lparen,rparen) = match psi with
                                                                                      And (_::_::_) -> ("(",")")
                                                                                    | Biimp(_,_)   -> ("(",")")
                                                                                    | _     -> ("","")
                                                                                  in
                                                                                  lparen ^ show psi ^ rparen
                                                           ) psis)
                           end
                        | Biimp(phi,psi) -> let (lparen,rparen) = match phi with
                                                                        Lit(_,_,_) -> ("","")
                                                                      | _          -> ("(",")")
                                            in
                                            let (lparen',rparen') = match psi with
                                                                          Lit(_,_,_) -> ("","")
                                                                        | _          -> ("(",")")
                                            in
                                            lparen ^ show phi ^ rparen ^ " <-> " ^ lparen' ^ show psi ^ rparen'
  in
  show

let showClause = function [] -> "{}"
                        | cl -> "{ " ^ String.concat ", " (List.map showFormula cl) ^ " }"

let showCNF = function []   -> "{}"
                     | [[]] -> "{{}}"
                     | cls  -> "{ " ^  String.concat " , " (List.map showClause cls) ^ " }"

let showModel lits = String.concat ", " (List.map (function Lit(_,_,_) as l -> showFormula l  
                                                          | _ -> failwith "propFormula.showModel: Expected a literal!")
                                           (List.filter (function Lit(b,_,_) -> if b then !visible_literals >= 0 else !visible_literals <= 0
                                                                 | _ -> failwith "propFormula.showModel: Expected a literal!") lits))

(* 
tidy returns a formula with the following properties:
- True or False only occur at top level.
- A conjunct is not a conjunction itself; a disjunct is not a disjunction itself. 
- Each conjunction and disjunction has at least two conjuncts, resp. disjuncts.
*)
let rec tidy =
  let rec flattenAnd acc = function []           -> acc
                                  | True::fs     -> flattenAnd acc fs
                                  | False::_     -> [False]
                                  | (And gs)::fs -> flattenAnd acc (gs @ fs)
                                  | phi::fs      -> flattenAnd (phi::acc) fs
  in
  let rec flattenOr acc = function []           -> acc
                                 | False::fs    -> flattenOr acc fs
                                 | True::_      -> [True]
                                 | (Or gs)::fs  -> flattenOr acc (gs @ fs)
                                 | phi::fs      -> flattenOr (phi::acc) fs
  in
  let rec negate = function True        -> False
                          | False       -> True
                          | Lit(b,x,ps) -> Lit(not b,x,ps)
                          | And fs      -> Or (List.map negate fs)
                          | Or fs       -> And (List.map negate fs)
                          | Biimp(f,g)  -> Biimp(negate f,g)
  in                                                 
  function And fs -> begin
                       let fs' = flattenAnd [] (List.map tidy fs) in
                       match fs' with []  -> True
                                    | [f] -> f
                                    | _   -> And fs'
                     end
         | Or fs  -> begin
                       let fs' = flattenOr [] (List.map tidy fs) in
                       match fs' with []  -> False
                                    | [f] -> f
                                    | _   -> Or fs'
                     end
         | Biimp(f,g) -> begin
                           let f' = tidy f in
                           match f' with
                                 True  -> tidy g
                               | False -> tidy (negate g)
                               | _     -> (let g' = tidy g in
                                           match g' with
                                             True -> f'
                                           | False -> tidy (negate f)
                                           | _     -> Biimp(f', g'))
                         end
         | f          -> f
  

(* expects the input to have been passed through the function tidy! *)
let toCNF phi =
  let nextIndex = ref 0 in
  let getNextAuxLit _ = let i = !nextIndex in
                        nextIndex := !nextIndex + 1;
                        Lit(true,"_Aux" ^ string_of_int i,[])
  in
  let negate = function Lit(b,x,ps) -> Lit(not b,x,ps)
                      | f             -> failwith ("Function toCNF.negate applied to non-literal `" ^ showFormula f ^ "': not allowed!")
  in
  
  let extraClauses = ref [] in
  let addClause cl = extraClauses := cl :: !extraClauses
  in
  let addDefAbbrAnd(x,ls) = List.iter (fun l -> addClause [negate x; l]) ls;
                            addClause (x::(List.map negate ls))
  in
  let addDefAbbrOr(x,ls) = List.iter (fun l -> addClause [x; negate l]) ls;
                           addClause ((negate x)::ls)
  in
  let addDefAbbrBiimp(x,l1,l2) = addClause [ negate x; negate l1; l2 ];
                                 addClause [ negate x; l1; negate l2 ];
                                 addClause [ x; negate l1; negate l2 ];
                                 addClause [ x; l1; l2 ]
  in
  let rec process = function And fs -> let ls = List.map process fs in
                                       let x = getNextAuxLit () in
                                       addDefAbbrAnd(x,ls);
                                       x 
                           | Or fs  -> let ls = List.map process fs in
                                       let x = getNextAuxLit () in
                                       addDefAbbrOr(x,ls);
                                       x
                           | Biimp(f1,f2) -> let l1 = process f1 in
                                             let l2 = process f2 in
                                             let x = getNextAuxLit () in
                                             addDefAbbrBiimp(x,l1,l2);
                                             x
                           | f      -> f
  in
  let rec processSecondOr = function True       -> failwith "toCNF.processSecondOr: unexpected constant True!"
                                   | False      -> failwith "toCNF.processSecondOr: unexpected constant False!"
                                   | Or fs      -> List.map process fs
                                   | And _      -> failwith "toCNF.processSecondOr: unexpected And!"
                                   | f          -> [ process f ]
  in
  let rec processFirstAnd = function True       -> []
                                   | False      -> [[]]
                                   | And fs     -> List.map processSecondOr fs
                                   | f          -> [ processSecondOr f ]
  in
  let result = ref [[]] in
  result := processFirstAnd phi;
  !result @ !extraClauses


module PropSet = Set.Make(
  struct
    type t = string * (int list)

    let compare = compare
  end);;

let collect_propositions =
  let rec collect = function Biimp(f,g)  -> PropSet.union (collect f) (collect g)
                           | And fs      -> List.fold_left (fun s -> fun f -> PropSet.union s (collect f)) PropSet.empty fs
                           | Or fs       -> List.fold_left (fun s -> fun f -> PropSet.union s (collect f)) PropSet.empty fs
                           | Lit(_,x,ps) -> PropSet.singleton (x,ps)
                           | _           -> PropSet.empty
  in
  collect  
