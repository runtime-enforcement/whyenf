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
open Formula

let debug m = if !debug then Stdio.print_endline ("[debug] formula_parser: " ^ m)

%}

%token LPA
%token RPA
%token LBR
%token RBR
%token COMMA
%token SEMICOLON
%token DOT
%token COL
%token EOF

%token <Interval.t> INTERVAL
%token <string> STR
%token <string> QSTR
%token <int> INT

%token FALSE
%token TRUE
%token EQCONST
%token LT GT
%token NEG
%token AND
%token OR
%token IMP
%token IFF
%token EXISTS
%token FORALL
%token PREV
%token NEXT
%token ONCE
%token EVENTUALLY
%token HISTORICALLY
%token ALWAYS
%token SINCE
%token UNTIL
%token RELEASE
%token TRIGGER

%token ADD SUB MUL DIV CONC
%token SUM AVG MED CNT MIN MAX

%token LET
%token IN

(* %nonassoc LET IN *)
%nonassoc LT GT EQCONST

%left ADD SUB
%left MUL DIV
%left CONC

%nonassoc INTERVAL
%right SINCE UNTIL RELEASE TRIGGER
%nonassoc PREV NEXT ONCE EVENTUALLY HISTORICALLY ALWAYS
%nonassoc EXISTS FORALL
%right IFF IMP
%left OR
%left AND
%nonassoc NEG

%type <Formula.t> formula
%start formula

%%

formula:
| e EOF                                  { debug "formula"; $1 }

e:
| LPA e RPA                              { debug "( e )"; $2 }
| TRUE                                   { debug "TRUE"; tt }
| FALSE                                  { debug "FALSE"; ff }
| LET pletp EQCONST e IN e %prec EQCONST { debug "LET"; match $2 with
                                                       | (r, vars) ->
                                                          flet (r, vars) $4 $6
                                                       | _ -> raise (Invalid_argument
                                                                       "invalid let definition") }
| LBR term EQCONST const RBR           { debug "EQCONST"; eqconst $2 (Pred.Term.unconst $4)}
| STR EQCONST aggregation LPA term SEMICOLON vars2 SEMICOLON e RPA
                                       { debug "AGG"; agg $1 $3 $5 $7 $9 }
| NEG e                                { debug "NEG e"; neg $2 }
| PREV INTERVAL e                      { debug "PREV INTERVAL e"; prev $2 $3 }
| PREV e                               { debug "PREV e"; prev Interval.full $2 }
| NEXT INTERVAL e                      { debug "NEXT INTERVAL e"; next $2 $3 }
| NEXT e                               { debug "NEXT e"; next Interval.full $2 }
| ONCE INTERVAL e                      { debug "ONCE INTERVAL e"; once $2 $3 }
| ONCE e                               { debug "ONCE e"; once Interval.full $2 }
| EVENTUALLY INTERVAL e                { debug "EVENTUALLY INTERVAL e"; (*Interval.is_bounded_exn "eventually" $2;*) eventually $2 $3 }
| EVENTUALLY e                         { debug "EVENTUALLY e"; (*raise (Invalid_argument "unbounded future operator: eventually")*) eventually Interval.full $2 }
| HISTORICALLY INTERVAL e              { debug "HISTORICALLY INTERVAL e"; historically $2 $3 }
| HISTORICALLY e                       { debug "HISTORICALLY e"; historically Interval.full $2 }
| ALWAYS INTERVAL e                    { debug "ALWAYS INTERVAL e"; (*Interval.is_bounded_exn "always" $2;*) always $2 $3 }
| ALWAYS e                             { debug "ALWAYS e"; (*raise (Invalid_argument "unbounded future operator: always")*) always Interval.full $2 }
| e AND side e                         { debug "e AND side e"; conj $3 $1 $4 }
| e AND e                              { debug "e AND e"; conj N $1 $3 }
| e OR side e                          { debug "e OR side e"; disj $3 $1 $4 }
| e OR e                               { debug "e OR e"; disj N $1 $3 }
| e IMP side e                         { debug "e IMP side e"; imp $3 $1 $4 }
| e IMP e                              { debug "e IMP e"; imp N $1 $3 }
| e IFF sides e                        { debug "e IFF sides e"; iff (fst $3) (snd $3) $1 $4 }
| e IFF e                              { debug "e IFF e"; iff N N $1 $3 }
| e SINCE INTERVAL side e              { debug "e SINCE INTERVAL side e"; since $4 $3 $1 $5 }
| e SINCE INTERVAL e                   { debug "e SINCE INTERVAL side e"; since N $3 $1 $4 }
| e SINCE side e                       { debug "e SINCE side e"; since $3 Interval.full $1 $4 }
| e SINCE e                            { debug "e SINCE e"; since N Interval.full $1 $3 }
| e UNTIL INTERVAL side e              { debug "e UNTIL INTERVAL side e"; (*Interval.is_bounded_exn "until" $4;*) until $4 $3 $1 $5 }
| e UNTIL INTERVAL e                   { debug "e UNTIL INTERVAL e"; (*Interval.is_bounded_exn "until" $4;*) until N $3 $1 $4 }
| e UNTIL side e                       { debug "e UNTIL side e"; (*raise (Invalid_argument "unbounded future operator: until")*) until $3 Interval.full $1 $4 }
| e UNTIL e                            { debug "e UNTIL e"; (*raise (Invalid_argument "unbounded future operator: until")*) until N Interval.full $1 $3 }
| e TRIGGER INTERVAL side e            { debug "e TRIGGER INTERVAL side e"; trigger $4 $3 $1 $5 }
| e TRIGGER INTERVAL e                 { debug "e TRIGGER INTERVAL e"; trigger N $3 $1 $4 }
| e TRIGGER side e                     { debug "e TRIGGER side e"; trigger $3 Interval.full $1 $4 }
| e TRIGGER e                          { debug "e TRIGGER e"; trigger N Interval.full $1 $3 }
| e RELEASE INTERVAL side e            { debug "e RELEASE INTERVAL side e"; (*Interval.is_bounded_exn "release" $3;*) release $4 $3 $1 $5 }
| e RELEASE INTERVAL e                 { debug "e RELEASE INTERVAL e"; (*Interval.is_bounded_exn "release" $3;*) release N $3 $1 $4 }
| e RELEASE side e                     { debug "e RELEASE side e"; (*raise (Invalid_argument "unbounded future operator: release")*) release $3 Interval.full $1 $4 }
| e RELEASE e                          { debug "e RELEASE e"; (*raise (Invalid_argument "unbounded future operator: release")*) release N Interval.full $1 $3 }
| EXISTS vars DOT e %prec EXISTS       { debug "EXISTS STR DOT e"; List.fold_right exists (List.tl $2) (exists (List.hd $2) $4) }
| FORALL vars DOT e %prec FORALL       { debug "FORALL STR DOT e"; List.fold_right forall (List.tl $2) (forall (List.hd $2) $4) }
| STR LPA terms RPA                    { debug "STR LPA terms RPA"; predicate $1 $3 }

pletp:
| STR LPA vars RPA                     { debug "STR LPA vars RPA"; letp $1 $3 }

side:
| COL STR                              { debug "COL STR"; Side.of_string $2 }
| COL RELEASE                          { debug "COL RELEASE"; Side.of_string "R" }

sides:
| COL STR COMMA STR                    { debug "COL STR COMMA STR"; (Side.of_string $2, Side.of_string $4) }

term:
| LPA term RPA             { debug "LPA term RPA"; $2 }
| const                    { debug "const"; $1 }
| STR                      { debug "STR"; Pred.Term.Var $1 }
| STR LPA terms RPA        { debug "STR LPA terms RPA"; Pred.Term.App ($1, $3) }
| term ADD term            { debug "term ADD term"; Pred.Term.App ("add", [$1; $3]) }
| term SUB term            { debug "term SUB term"; Pred.Term.App ("sub", [$1; $3]) }
| term MUL term            { debug "term MUL term"; Pred.Term.App ("mul", [$1; $3]) }
| term DIV term            { debug "term DIV term"; Pred.Term.App ("div", [$1; $3]) }
| term EQCONST EQCONST term { debug "term EQ EQ term"; Pred.Term.App ("eq", [$1; $4]) }
| term LT GT term          { debug "term LT GT term"; Pred.Term.App ("neq", [$1; $4]) }
| term LT term             { debug "term LT term"; Pred.Term.App ("lt", [$1; $3]) }
| term LT EQCONST term     { debug "term LT EQCONST term"; Pred.Term.App ("leq", [$1; $4]) }
| term GT term             { debug "term GT term"; Pred.Term.App ("gt", [$1; $3]) }
| term GT EQCONST term     { debug "term GT EQCONST term"; Pred.Term.App ("geq", [$1; $4]) }
| term ADD DOT term %prec ADD { debug "term ADD DOT term"; Pred.Term.App ("fadd", [$1; $4]) }
| term SUB DOT term %prec SUB { debug "term SUB DOT term"; Pred.Term.App ("fsub", [$1; $4]) }
| term MUL DOT term %prec MUL { debug "term MUL DOT term"; Pred.Term.App ("fmul", [$1; $4]) }
| term MUL MUL term        { debug "term MUL MUL term"; Pred.Term.App ("pow", [$1; $4]) }
| term DIV DOT term %prec DIV { debug "term DIV DOT term"; Pred.Term.App ("fdiv", [$1; $4]) }
| term EQCONST EQCONST DOT term %prec EQCONST { debug "term EQ EQ DOT term"; Pred.Term.App ("feq", [$1; $5]) }
| term LT GT DOT term %prec GT { debug "term LT GT DOT term"; Pred.Term.App ("fneq", [$1; $5]) }
| term LT DOT term %prec LT { debug "term LT DOT term"; Pred.Term.App ("flt", [$1; $4]) }
| term LT EQCONST DOT term %prec EQCONST { debug "term LT EQCONST DOT term"; Pred.Term.App ("fleq", [$1; $5]) }
| term GT DOT term %prec GT { debug "term GT DOT term"; Pred.Term.App ("fgt", [$1; $4]) }
| term GT EQCONST DOT term %prec EQCONST { debug "term GT EQCONST DOT term"; Pred.Term.App ("fgeq", [$1; $5]) }
| term CONC term           { debug "term CONC term"; Pred.Term.App ("conc", [$1; $3]) }

const:
| INT                                  { debug "INT"; Pred.Term.Const (Int $1) }
| QSTR                                 { debug "QSTR"; Pred.Term.Const (Str (Etc.unquote $1)) }

terms:
| trms=separated_list (COMMA, term)    { debug "trms"; trms }

vars:
| vrs=separated_nonempty_list (COMMA, STR) { debug "vrs"; vrs }

vars2:
| vrs=separated_list (COMMA, STR) { debug "vrs"; vrs }

aggregation:
| SUM { debug "SUM"; Aggregation.ASum }
| AVG { debug "AVG"; Aggregation.AAvg }
| MED { debug "MED"; Aggregation.AMed }
| CNT { debug "CNT"; Aggregation.ACnt }
| MIN { debug "MIN"; Aggregation.AMin }
| MAX { debug "MAX"; Aggregation.AMax }
