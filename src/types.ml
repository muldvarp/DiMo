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
