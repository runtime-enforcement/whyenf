%{
(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Etc
open Sformula

let debug m = if !debug then Stdio.print_endline ("[debug] formula_parser: " ^ m)

%}

%token LPA RPA
%token COMMA SEMICOLON DOT COL GETS LET IN
%token EOF

%token <Interval.t> INTERVAL
%token <string>     STR
%token <string>     QSTR
%token <int>        INT
%token <float>      FLOAT
%token FALSE TRUE

%token NOT
%token LT GT LEQ GEQ EQ NEQ
%token AND OR IMP IFF
%token EXISTS FORALL
%token PREV NEXT ONCE EVENTUALLY HISTORICALLY ALWAYS
%token SINCE UNTIL RELEASE TRIGGER
%token ADD SUB MUL DIV POW CONC
%token FADD FSUB FMUL FDIV FPOW
%token SUM AVG MED CNT MIN MAX


%left IN
%left SEMICOLON
%left EXISTS FORALL

%left IFF
%right IMP
%left OR
%left AND
%nonassoc SINCE UNTIL RELEASE TRIGGER
%left PREV NEXT ONCE EVENTUALLY HISTORICALLY ALWAYS
%nonassoc LT GT LEQ GEQ EQ NEQ
%left ADD SUB FADD FSUB CONC
%left MUL DIV FMUL FDIV
%left POW FPOW
%left NOT

%type <Sformula.t> formula
%start formula

%%

formula:
| e EOF                                     { debug "formula"; $1 }

e:
| LPA e RPA                                 { debug "( e )"; $2 }
| const                                     { debug "const"; SConst $1 }
| STR LPA terms RPA                         { debug "STR LPA terms RPA"; SApp ($1, $3) }
| STR                                       { debug "STR"; SVar $1 }
| LET pletp EQ e IN e %prec IN              { debug "LET"; SLet (fst $2, snd $2, $4, $6) }
| STR GETS aop LPA e SEMICOLON vars_or_empty SEMICOLON e RPA
                                            { debug "AGG"; SAgg ($1, $3, $5, $7, $9) }
| e SEMICOLON STR GETS e %prec SEMICOLON    { debug "AGG"; SAssign ($1, $3, $5) }
| uop e                                     { debug "uop e"; SUop ($1, $2) }
| e AND side e %prec AND                    { debug "e AND side e"; SBop (Some $3, $1, Bop.BAnd, $4) }
| e OR side e %prec OR                      { debug "e OR side e"; SBop (Some $3, $1, Bop.BOr, $4) }
| e IMP side e %prec IMP                    { debug "e IMP side e"; SBop (Some $3, $1, Bop.BImp, $4) }
| e bop e                                   { debug "e bop e"; SBop (None, $1, $2, $3) }
| e bop2 sides e %prec IFF                  { debug "e bop2 sides e"; SBop2 (Some $3, $1, $2, $4) }
| e bop2 e                                  { debug "e bop2 e"; SBop2 (None, $1, $2, $3) }
| utop INTERVAL e %prec PREV                { debug "utop INTERVAL e"; SUtop ($2, $1, $3) }
| utop e                                    { debug "utop e"; SUtop (Interval.full, $1, $2) }
| e btop INTERVAL side e %prec SINCE        { debug "e btop INTERVAL side e"; SBtop (Some $4, $3, $1, $2, $5) }
| e btop INTERVAL e %prec SINCE             { debug "e btop INTERVAL e"; SBtop (None, $3, $1, $2, $4) }
| e btop side e %prec SINCE                 { debug "e btop side e"; SBtop (Some $3, Interval.full, $1, $2, $4) }
| e btop e                                  { debug "e btop e"; SBtop (None, Interval.full, $1, $2, $3) }
| EXISTS vars DOT e %prec EXISTS            { debug "EXISTS vars DOT e"; SExists ($2, $4) }
| FORALL vars DOT e %prec FORALL            { debug "FORALL vars DOT e"; SForall ($2, $4) }

terms:
| separated_list (COMMA, e)                 { debug "trms"; $1 }

vars:
| separated_nonempty_list (COMMA, STR)      { debug "vrs"; $1 }

vars_or_empty:
| separated_list (COMMA, STR)               { debug "vrs"; $1 }

%inline pletp:
| STR LPA vars_or_empty RPA                 { debug "pletp"; ($1, $3) }

%inline uop:
| SUB                                       { Uop.USub }
| FSUB                                      { Uop.UFSub }
| NOT                                       { Uop.UNot }

%inline bop:
| lbop                                      { $1 }
| ADD                                       { Bop.BAdd }
| SUB                                       { Bop.BSub }
| MUL                                       { Bop.BMul }
| DIV                                       { Bop.BDiv }
| POW                                       { Bop.BPow }
| FADD                                      { Bop.BFAdd }
| FSUB                                      { Bop.BFSub }
| FMUL                                      { Bop.BFMul }
| FDIV                                      { Bop.BFDiv }
| FPOW                                      { Bop.BFPow }
| EQ                                        { Bop.BEq }
| NEQ                                       { Bop.BNeq }
| LT                                        { Bop.BLt }
| LEQ                                       { Bop.BLeq }
| GT                                        { Bop.BGt }
| GEQ                                       { Bop.BGeq }
| CONC                                      { Bop.BConc }

%inline lbop:
| AND                                       { Bop.BAnd }
| OR                                        { Bop.BOr }
| IMP                                       { Bop.BImp }

%inline bop2:
| IFF                                       { Bop2.BIff }

%inline utop:
| PREV                                      { Utop.UPrev }
| NEXT                                      { Utop.UNext }
| ALWAYS                                    { Utop.UAlways }
| HISTORICALLY                              { Utop.UHistorically }
| EVENTUALLY                                { Utop.UEventually }
| ONCE                                      { Utop.UOnce }

%inline btop:
| SINCE                                     { Btop.BSince }
| UNTIL                                     { Btop.BUntil }
| RELEASE                                   { Btop.BRelease }
| TRIGGER                                   { Btop.BTrigger }

%inline side:
| COL STR                                   { debug "COL STR"; Side.of_string $2 }
| COL RELEASE                               { debug "COL RELEASE"; Side.of_string "R" }

%inline sides:
| COL STR COMMA STR                         { debug "COL STR COMMA STR"; (Side.of_string $2, Side.of_string $4) }

%inline const:
| TRUE                                      { debug "TRUE"; Const.CBool true }                                    
| FALSE                                     { debug "FALSE"; Const.CBool false }                                    
| INT                                       { debug "INT"; Const.CInt $1 }
| FLOAT                                     { debug "FLOAT"; Const.CFloat $1 }
| QSTR                                      { debug "QSTR"; Const.CStr $1 }

%inline aop:
| SUM                                       { debug "SUM"; Aop.ASum }
| AVG                                       { debug "AVG"; Aop.AAvg }
| MED                                       { debug "MED"; Aop.AMed }
| CNT                                       { debug "CNT"; Aop.ACnt }
| MIN                                       { debug "MIN"; Aop.AMin }
| MAX                                       { debug "MAX"; Aop.AMax }
