/* File parser.mly */
/* The Header */
%{
  open Alschemes		   
%}
/* The Grammar */
%token <string> TVAR
%token <string> TPARAM
%token <int> TINT
%token <string * (int -> int)> TUNOP 
%token <string * (int -> int -> int)> TBINOP
%token TPLUS, TMULT, TDIV
%token TMIN TMAX
%token TAND TOR TNEG TIMP TBIIMP TTRUE TFALSE
%token TALL TSOME TCOLON TDOT
%token TLPAREN TRPAREN TLBRACE TRBRACE
%token TCOMMA TDOTS
%token TNAT
%token TPROPOSITIONS TPARAMETERS TFORMULAS TWITH TSATISFIABLE TVALID TEQUIVALENT TMODELS TGENEQUIV TTO
%token <(int -> int -> bool)> TCOMP
%token TEQ
%token TEOF

/* lowest precedence */
%right TCOMMA
%right TEQUAL
%right TDOT
%right TBIIMP
%right TIMP
%right TOR 
%right TAND
%right TCOLON
%left  TPLUS
%left  TNEG
%left  TMULT
%left  TDIV
%right TBINOP
/* highest precedence */

%start start             /* the entry point */
%type <Alschemes.problem>                start
%type <Alschemes.problem>                main
%type <string * Alschemes.domain>        param
%type <Alschemes.domain>                 domain
%type <Alschemes.alScheme>               scheme
%type <((string * Alschemes.domain) list) * Alschemes.constraints> parameters
%type <Alschemes.symbSet>                symbset
%type <Alschemes.intTerm>                term
%type <Alschemes.intTerm list>           terms
%%
start:	  main TEOF                                                     { $1 }
;
main:	  TSATISFIABLE scheme propositions parameters definitions            { let (params,constrs) = $4 in ProblemSat($3,params,constrs,$2,$5) }
	| TVALID scheme propositions parameters definitions                  { let (params,constrs) = $4 in ProblemVal($3,params,constrs,$2,$5) }
	| TEQUIVALENT scheme TTO scheme propositions parameters definitions  { let (params,constrs) = $6 in ProblemEquiv($5,params,constrs,$2,$4,$7) }
	| TMODELS scheme propositions parameters definitions                 { let (params,constrs) = $4 in ProblemModels($3,params,constrs,$2,$5) }

;
propositions:                                                           { StringSet.empty }
        | TPROPOSITIONS props                                           { $2 }
;
props:  |                                                               { StringSet.empty }
	| TVAR                                                          { StringSet.singleton $1 }
	| TVAR TCOMMA props                                             { StringSet.add $1 $3 }
;
parameters:                                                             { ( [], [] ) } 
        | TPARAMETERS params                                            { ( $2, [] ) }
        | TPARAMETERS params TWITH constraints                          { ( $2, $4 ) }
;
params: 
	| param                                                         { [ $1 ] }
        | param TCOMMA params                                           { $1 :: $3 }
;
param: 	TPARAM TCOLON domain                                            { ($1,$3) }
;
domain:
          TNAT                                                          { From(0,1) }
	| TLBRACE TINT TCOMMA TDOTS TRBRACE                             { From($2,1) }
	| TLBRACE TINT TCOMMA TDOTS TCOMMA TINT TRBRACE                 { FromTo($2,1,$6) }
	| TLBRACE TINT TCOMMA TINT TCOMMA TDOTS TRBRACE                 { From($2,$4-$2) }
	| TLBRACE TINT TCOMMA TINT TCOMMA TDOTS TCOMMA TINT TRBRACE     { FromTo($2,$4-$2,$8) }
	| TLBRACE constants TRBRACE                                     { FinSet($2) }
;

constants:
          TINT                                                          { [ $1 ] }
	| TINT TCOMMA constants                                         { $1 :: $3 }
constraints:
          cnstr                                                         { [ $1 ] }
	| cnstr TCOMMA constraints                                      { $1 :: $3 }
;

cnstr:    TPARAM TCOMP TPARAM                                           { ($1,$2,$3) }
	| TPARAM TEQ TPARAM                                             { ($1,(=),$3) }
;

name:     TVAR                                                          { ($1,[]) }
	| TVAR TLPAREN TRPAREN                                          { ($1,[]) }
	| TVAR TLPAREN uparams TRPAREN                                  { ($1,$3) }
;

uparams:  TPARAM                                                        { [ $1 ] }
	| TPARAM TCOMMA uparams                                         { $1 :: $3 }
;

definitions:                                                            { [] }
        | TFORMULAS formulas                                            { $2 }
;
  
formulas:                                                               { [] }
	| formula formulas                                              { $1 :: $2 }
;

formula:  pattern TEQ scheme                                            { let (name,params) = $1 in (name, params, $3) }
;

pattern:  TVAR                                                          { ($1, []) }
        | TVAR TLPAREN TRPAREN                                          { ($1, []) }
	| TVAR TLPAREN paramorconsts TRPAREN                            { ($1, $3) }
;

paramorconsts:
          TPARAM                                                        { [ Param($1) ] }
	| TINT                                                          { [ Const($1) ] }
	| TPARAM TCOMMA paramorconsts                                   { (Param($1)) :: $3 }
	| TINT TCOMMA paramorconsts                                     { (Const($1)) :: $3 }
;

scheme:
          TTRUE                                                         { STrue }
	| TFALSE                                                        { SFalse } 
        | TVAR                                                          { SPred($1,[]) }
        | TVAR TLPAREN TRPAREN                                          { SPred($1,[]) }
        | TVAR TLPAREN terms TRPAREN                                    { SPred($1,$3) }
        | TNEG scheme                                                   { SNeg($2) }
        | scheme TAND scheme                                            { SAnd($1,$3) }
	| scheme TOR scheme                                             { SOr($1,$3) }
	| scheme TIMP scheme                                            { SImp($1,$3) }
	| scheme TBIIMP scheme                                          { SBiimp($1,$3) }
        | TALL TPARAM TCOLON symbset TDOT scheme                        { SForall($2,$4,$6) }
        | TSOME TPARAM TCOLON symbset TDOT scheme                       { SForsome($2,$4,$6) }
	| TLPAREN scheme TRPAREN                                        { $2 }
;

symbset:
          TLBRACE terms TRBRACE                                         { SmallSet($2) }
        | TLBRACE term TCOMMA term TCOMMA TDOTS TCOMMA term TRBRACE     { Enumeration($2,$4,$8) }
        | TLBRACE term TCOMMA TDOTS TCOMMA term TRBRACE                 { Enumeration($2,BinOp("+",$2,Const(1),(+)),$6) }
	| symbset TOR symbset                                           { BinSetOp("|",$1,$3,IntSet.union) }
	| symbset TAND symbset                                          { BinSetOp("&",$1,$3,IntSet.inter) }
	| symbset TNEG symbset                                          { BinSetOp("\\",$1,$3,IntSet.diff) }
;

term:
	  TINT                                                          { Const($1) }
	| TPARAM                                                        { Param($1) }
	| term TBINOP term                                              { let (s,f) = $2 in BinOp(s,$1,$3,f) }
	| term TPLUS term						{ BinOp("+",$1,$3,(+)) }
	| term TMULT term						{ BinOp("*",$1,$3,(fun x -> fun y -> x*y)) }
	| term TNEG term                                                { BinOp("-",$1,$3,(fun x -> fun y -> x-y)) }
	| term TDIV term						{ BinOp("/",$1,$3,(/)) }
	| TUNOP term                                                    { let (s,f) = $1 in UnOp(s,$2,f) }
	| TMIN symbset                                                  { let bmin m = try
	  						                                  IntSet.min_elt m 
						                                       with Not_found -> 0
								          in SetOp("MIN",$2,bmin) }
	| TMAX symbset                                                  { let bmax m = try
	  						                                  IntSet.max_elt m 
						                                       with Not_found -> 0
								          in SetOp("MAX",$2,bmax) }
	| TLPAREN term TRPAREN                                          { $2 }
;

terms:
	  term                                                          { [ $1 ] }
	| term TCOMMA terms                                             { $1 :: $3 }
;
