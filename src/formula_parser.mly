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
%token COMMA
%token DOT
%token EOF

%token <Interval.t> INTERVAL
%token <string> STR
%token <string> QSTR
%token <int> INT

%token FALSE
%token TRUE
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
| e EOF                                { debug "formula"; $1 }

e:
| LPA e RPA                            { debug "( e )"; $2 }
| TRUE                                 { debug "TRUE"; tt }
| FALSE                                { debug "FALSE"; ff }
| NEG e                                { debug "NEG e"; neg $2 }
| PREV INTERVAL e                      { debug "PREV INTERVAL e"; prev $2 $3 }
| PREV e                               { debug "PREV e"; prev Interval.full $2 }
| NEXT INTERVAL e                      { debug "NEXT INTERVAL e"; next $2 $3 }
| NEXT e                               { debug "NEXT e"; next Interval.full $2 }
| ONCE INTERVAL e                      { debug "ONCE INTERVAL e"; once $2 $3 }
| ONCE e                               { debug "ONCE e"; once Interval.full $2 }
| EVENTUALLY INTERVAL e                { debug "EVENTUALLY INTERVAL e"; eventually $2 $3 }
| EVENTUALLY e                         { debug "EVENTUALLY e"; eventually Interval.full $2 }
| HISTORICALLY INTERVAL e              { debug "HISTORICALLY INTERVAL e"; historically $2 $3 }
| HISTORICALLY e                       { debug "HISTORICALLY e"; historically Interval.full $2 }
| ALWAYS INTERVAL e                    { debug "ALWAYS INTERVAL e"; always $2 $3 }
| ALWAYS e                             { debug "ALWAYS e"; always Interval.full $2 }
| e AND e                              { debug "e AND e"; conj $1 $3 }
| e OR e                               { debug "e OR e"; disj $1 $3 }
| e IMP e                              { debug "e IMP e"; imp $1 $3 }
| e IFF e                              { debug "e IFF e"; iff $1 $3 }
| e SINCE INTERVAL e                   { debug "e SINCE INTERVAL e"; since $3 $1 $4 }
| e SINCE e                            { debug "e SINCE e"; since Interval.full $1 $3 }
| e UNTIL INTERVAL e                   { debug "e UNTIL INTERVAL e"; until $3 $1 $4 }
| e UNTIL e                            { debug "e UNTIL e"; until Interval.full $1 $3 }
| e TRIGGER INTERVAL e                 { debug "e TRIGGER INTERVAL e"; trigger $3 $1 $4 }
| e TRIGGER e                          { debug "e TRIGGER e"; trigger Interval.full $1 $3 }
| e RELEASE INTERVAL e                 { debug "e RELEASE INTERVAL e"; release $3 $1 $4 }
| e RELEASE e                          { debug "e RELEASE e"; release Interval.full $1 $3 }
| EXISTS STR DOT e %prec EXISTS        { debug "EXISTS STR DOT e"; exists $2 $4 }
| FORALL STR DOT e %prec FORALL        { debug "FORALL STR DOT e"; forall $2 $4 }
| STR LPA terms RPA                    { debug "STR LPA terms RPA"; predicate $1 $3 }

term:
| const                                { debug "CONST"; $1 }
| STR                                  { debug "VAR"; Pred.Term.Var $1 }

const:
| INT                                  { debug "INT"; Pred.Term.Const (Int $1) }
| QSTR                                 { debug "QSTR"; Pred.Term.Const (Str (Etc.unquote $1)) }

terms:
| trms=separated_list (COMMA, term)    { debug "trms"; trms }
