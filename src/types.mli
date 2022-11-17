module IntSet :
  sig
    type elt = int
    type t
    val empty : t
    val is_empty : t -> bool
    val mem : elt -> t -> bool
    val add : elt -> t -> t
    val singleton : elt -> t
    val remove : elt -> t -> t
    val union : t -> t -> t
    val inter : t -> t -> t
    val diff : t -> t -> t
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val subset : t -> t -> bool
    val iter : (elt -> unit) -> t -> unit
    val map : (elt -> elt) -> t -> t
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all : (elt -> bool) -> t -> bool
    val exists : (elt -> bool) -> t -> bool
    val filter : (elt -> bool) -> t -> t
    val partition : (elt -> bool) -> t -> t * t
    val cardinal : t -> int
    val elements : t -> elt list
    val min_elt : t -> elt
    val min_elt_opt : t -> elt option
    val max_elt : t -> elt
    val max_elt_opt : t -> elt option
    val choose : t -> elt
    val choose_opt : t -> elt option
    val split : elt -> t -> t * bool * t
    val find : elt -> t -> elt
    val find_opt : elt -> t -> elt option
    val find_first : (elt -> bool) -> t -> elt
    val find_first_opt : (elt -> bool) -> t -> elt option
    val find_last : (elt -> bool) -> t -> elt
    val find_last_opt : (elt -> bool) -> t -> elt option
    val of_list : elt list -> t
    val to_seq_from : elt -> t -> elt Seq.t
    val to_seq : t -> elt Seq.t
    val add_seq : elt Seq.t -> t -> t
    val of_seq : elt Seq.t -> t
  end

type intTerm =
    Const of int
  | Param of string
  | BinOp of string * intTerm * intTerm * (int -> int -> int)
  | UnOp of string * intTerm * (int -> int)
  | SetOp of string * symbSet * (IntSet.t -> int)

and symbSet =
    SmallSet of intTerm list
  | Enumeration of intTerm * intTerm * intTerm
  | BinSetOp of string * symbSet * symbSet *
      (IntSet.t -> IntSet.t -> IntSet.t)

type bexpr =
    HasModel
  | BNeg of bexpr
  | BAnd of bexpr * bexpr
  | BOr of bexpr * bexpr
  | Prop of string * intTerm list
  | BComp of intTerm * (int -> int -> bool) * intTerm

type outprog =
    PSkip
  | PExit
  | PPrint of string
  | PPrintf of string * intTerm list
  | PITEU of bexpr * outprog * outprog * outprog
  | PFor of string * intTerm * intTerm * intTerm * outprog
  | PComp of outprog * outprog
  | PForEach of string * outprog

type alScheme =
    STrue
  | SFalse
  | SPred of string * intTerm list
  | SNeg of alScheme
  | SAnd of alScheme * alScheme
  | SOr of alScheme * alScheme
  | SImp of alScheme * alScheme
  | SBiimp of alScheme * alScheme
  | SForall of string * symbSet * alScheme
  | SForsome of string * symbSet * alScheme

module StringSet :
  sig
    type elt = String.t
    type t = Set.Make(String).t
    val empty : t
    val is_empty : t -> bool
    val mem : elt -> t -> bool
    val add : elt -> t -> t
    val singleton : elt -> t
    val remove : elt -> t -> t
    val union : t -> t -> t
    val inter : t -> t -> t
    val diff : t -> t -> t
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val subset : t -> t -> bool
    val iter : (elt -> unit) -> t -> unit
    val map : (elt -> elt) -> t -> t
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all : (elt -> bool) -> t -> bool
    val exists : (elt -> bool) -> t -> bool
    val filter : (elt -> bool) -> t -> t
    val partition : (elt -> bool) -> t -> t * t
    val cardinal : t -> int
    val elements : t -> elt list
    val min_elt : t -> elt
    val min_elt_opt : t -> elt option
    val max_elt : t -> elt
    val max_elt_opt : t -> elt option
    val choose : t -> elt
    val choose_opt : t -> elt option
    val split : elt -> t -> t * bool * t
    val find : elt -> t -> elt
    val find_opt : elt -> t -> elt option
    val find_first : (elt -> bool) -> t -> elt
    val find_first_opt : (elt -> bool) -> t -> elt option
    val find_last : (elt -> bool) -> t -> elt
    val find_last_opt : (elt -> bool) -> t -> elt option
    val of_list : elt list -> t
    val to_seq_from : elt -> t -> elt Seq.t
    val to_seq : t -> elt Seq.t
    val add_seq : elt Seq.t -> t -> t
    val of_seq : elt Seq.t -> t
  end

type propositions = StringSet.t

type constraints = (string * (int -> int -> bool) * string) list

type domain =
    From of int * int
  | FromTo of int * int * int
  | FinSet of int list

type parameters = (string * domain) list

type definitions = (string * intTerm list * alScheme) list

type problem =
    ProblemSat of propositions * parameters * constraints * alScheme *
      definitions * outprog
  | ProblemVal of propositions * parameters * constraints * alScheme *
      definitions * outprog
  | ProblemEquiv of propositions * parameters * constraints * alScheme *
      alScheme * definitions
  | ProblemModels of propositions * parameters * constraints * alScheme *
      definitions * outprog

