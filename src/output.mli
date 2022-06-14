open Alschemes

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

val debug_level : int ref
                
val output : int -> int -> string -> unit
  
val announce_and_do : int -> int -> string -> 'a -> 'a
