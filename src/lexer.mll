(* File lexer.mll *)
{
open Parser        (* The type token is defined in parser.mli *)
}
rule token = parse
 | ([' ' '\t'])+                                      { token lexbuf  }
 | ['\n']                                             { Lexing.new_line lexbuf; token lexbuf  }   (* [' ' '\t' '\n' '\r']                               { token lexbuf } *)    (* skip blanks *)
 | "\"" [^ '\"']* "\""  as str                        { TSTRING(str) }
 | "(*" [^ '*']* '*' ( [^ ')'] [^ '*']* '*' )* ')'    { token lexbuf }  (* skip comments *)
 | "PROPOSITIONS"                                     { TPROPOSITIONS }
 | "PARAMETERS"                                       { TPARAMETERS }
 | "FORMULAS"                                         { TFORMULAS }
 | "OUTPUT"                                           { TOUTPUT }
 | "SATISFIABLE"                                      { TSATISFIABLE }
 | "VALID"                                            { TVALID }
 | "EQUIVALENT"                                       { TEQUIVALENT }
 | "MODELS"                                           { TMODELS }
 | "FROM"                                             { TFROM }
 | "TO"                                               { TTO }
 | "IF"                                               { TIF }
 | "THEN"                                             { TTHEN }
 | "ELSE"                                             { TELSE }
 | "UNDEF"                                            { TUNDEF}
 | "ENDIF"                                            { TENDIF }
 | "SKIP"                                             { TSKIP }
 | "PRINT"                                            { TPRINT }
 | "PRINTF"                                           { TPRINTF }
 | "FOR"                                              { TFOR }
 | "OF"                                               { TOF }
 | "STEP"                                             { TSTEP }
 | "DO"                                               { TDO }
 | "DONE"                                             { TDONE }
 | "HASMODEL"                                         { THASMODEL }
 | "FORALL"                                           { TALL }
 | "FORSOME"                                          { TSOME }
 | "MIN"                                              { TMIN }
 | "MAX"                                              { TMAX }
 | "EXIT"                                             { TEXIT }
 | "LOG"                                              { let rec log = function 0 -> failwith "LOG(0) undefined!"
                                                                             | 1 -> 0 
                                                                             | n -> 1 + log (n/2 + (n mod 2))
                                                        in TUNOP("LOG ",log) }
 | "FLOG"                                              { let rec log = function 0 -> failwith "LOG(0) undefined!"
                                                                              | 1 -> 0 
                                                                              | n -> 1 + log (n/2)
                                                        in TUNOP("FLOG ",log) }
 | "MOD"                                              { TBINOP("MOD",(mod)) }
 | "NAT"                                              { TNAT }
 | "WITH"                                             { TWITH }
 | '&'                                                { TAND }
 | '|'                                                { TOR }
 | "->"	                                              { TIMP }
 | "<->"                                     	      { TBIIMP }
 | '-'                                                { TNEG }
 | "True"                                             { TTRUE }
 | "False"                                            { TFALSE }
 | ['A'-'Z']['a'-'z' 'A'-'Z' '0'-'9' '_']*'\''* as id      { TVAR(id) }
 | ['a'-'z']['a'-'z' 'A'-'Z' '0'-'9' '_']*'\''* as id      { TPARAM(id) }
 | ['0'-'9']+ as lxm                                  { TINT(int_of_string lxm) }
 | '+'                                                { TPLUS }
 | '*'                                                { TMULT }
 | '/'                                                { TDIV }
 | '^'                                                { let rec pow a = function 0 -> 1
                                                                               | 1 -> a
                                                                               | n -> let b = pow a (n / 2) in
                                                                                      b * b * (if n mod 2 = 0 then 1 else a)
                                                        in TBINOP("^",pow) }
 | "<="                                                 { TCOMP((<=)) }
 | ">="                                                 { TCOMP((>=)) }
 | "<>"                                                 { TCOMP((<>)) }
 | '<'                                                  { TCOMP((<)) }
 | '>'                                                  { TCOMP((>)) }
 | '='                                                  { TEQ }
 | '('                                                  { TLPAREN }
 | ')'                                                  { TRPAREN }
 | '{'                                                  { TLBRACE }
 | '}'                                                  { TRBRACE }
 | '['                                                  { TLBRACKET }
 | ']'                                                  { TRBRACKET }
 | ".."                                                 { TDOTS }
 | '.'                                                  { TDOT }
 | ':'                                                  { TCOLON }
 | ';'                                                  { TSEMICOLON }
 | ','                                                  { TCOMMA }
 | eof                                                  { TEOF }


