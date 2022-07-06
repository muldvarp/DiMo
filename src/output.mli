open Alschemes

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

val debug_level : int ref
                
val output : int -> int -> string -> unit
  
val announce_and_do : int -> int -> string -> 'a -> 'a
