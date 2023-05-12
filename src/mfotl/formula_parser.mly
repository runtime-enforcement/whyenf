/*******************************************************************
 *     This is part of Explanator2, it is distributed under the    *
 *     terms of the GNU Lesser General Public License version 3    *
 *           (see file LICENSE for more details)                   *
 *                                                                 *
 *  Copyright 2023:                                                *
 *  Dmitriy Traytel (UCPH)                                         *
 *  Leonardo Lima (UCPH)                                           *
 *******************************************************************/

%{
open Formula
%}

%token LPA
%token RPA
%token COMMA
%token DOT
%token EOF

%token <Interval.t> INTERVAL
%token <string> STR

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
| e EOF                                { $1 }

e:
| LPA e RPA                            { $2 }
| TRUE                                 { tt }
| FALSE                                { ff }
| NEG e                                { neg $2 }
| PREV INTERVAL e                      { prev $2 $3 }
| PREV e                               { prev Interval.full $2 }
| NEXT INTERVAL e                      { next $2 $3 }
| NEXT e                               { next Interval.full $2 }
| ONCE INTERVAL e                      { once $2 $3 }
| ONCE e                               { once Interval.full $2 }
| EVENTUALLY INTERVAL e                { eventually $2 $3 }
| EVENTUALLY e                         { eventually Interval.full $2 }
| HISTORICALLY INTERVAL e              { historically $2 $3 }
| HISTORICALLY e                       { historically Interval.full $2 }
| ALWAYS INTERVAL e                    { always $2 $3 }
| ALWAYS e                             { always Interval.full $2 }
| e AND e                              { conj $1 $3 }
| e OR e                               { disj $1 $3 }
| e IMP e                              { imp $1 $3 }
| e IFF e                              { iff $1 $3 }
| e SINCE INTERVAL e                   { since $3 $1 $4 }
| e SINCE e                            { since Interval.full $1 $3 }
| e UNTIL INTERVAL e                   { until $3 $1 $4 }
| e UNTIL e                            { until Interval.full $1 $3 }
| e TRIGGER INTERVAL e                 { trigger $3 $1 $4 }
| e TRIGGER e                          { trigger Interval.full $1 $3 }
| e RELEASE INTERVAL e                 { release $3 $1 $4 }
| e RELEASE e                          { release Interval.full $1 $3 }
| EXISTS STR DOT e %prec EXISTS        { exists $2 $4 }
| FORALL STR DOT e %prec FORALL        { forall $2 $4 }
| STR LPA sterms RPA                   { predicate $1 $3 }

sterms:
| strms=separated_list (COMMA, STR)    { strms }
