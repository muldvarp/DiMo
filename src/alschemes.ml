open Enumerators ;;
open PropFormula ;;
open Types ;;

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
