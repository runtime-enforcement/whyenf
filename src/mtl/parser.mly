/*******************************************************************
 *     This is part of Explanator2, it is distributed under the    *
 *     terms of the GNU Lesser General Public License version 3    *
 *           (see file LICENSE for more details)                   *
 *                                                                 *
 *  Copyright 2021:                                                *
 *  Dmitriy Traytel (UCPH)                                         *
 *  Leonardo Lima (UCPH)                                           *
 *******************************************************************/

%{
open Interval
open Formula
%}

%token <string> ATOM
%token <Interval.interval> INTERVAL
%token LOPEN ROPEN
%token FALSE TRUE NEG CONJ DISJ IMP IFF EOF
%token SINCE UNTIL RELEASE TRIGGER
%token NEXT PREV ALWAYS EVENTUALLY HISTORICALLY ONCE

%nonassoc INTERVAL
%right IFF
%right IMP
%nonassoc PREV NEXT ALWAYS EVENTUALLY ONCE HISTORICALLY
%nonassoc SINCE UNTIL RELEASE TRIGGER
%left DISJ
%left CONJ
%nonassoc NEG

%type <Formula.formula> formula
%start formula

%%

formula:
| e EOF { $1 }

e:
| LOPEN e ROPEN           { $2 }
| TRUE                    { tt }
| FALSE                   { ff }
| e CONJ e                { conj $1 $3 }
| e DISJ e                { disj $1 $3 }
| e IMP e                 { imp $1 $3 }
| e IFF e                 { iff $1 $3 }
| NEG e                   { neg $2 }
| ATOM                    { p $1 }
| e SINCE INTERVAL e      { since $3 $1 $4 }
| e SINCE e               { since full $1 $3 }
| e TRIGGER INTERVAL e    { trigger $3 $1 $4 }
| e TRIGGER e             { trigger full $1 $3 }
| e UNTIL INTERVAL e      { until $3 $1 $4 }
| e UNTIL e               { until full $1 $3 }
| e RELEASE INTERVAL e    { release $3 $1 $4 }
| e RELEASE e             { release full $1 $3 }
| NEXT INTERVAL e         { next $2 $3 }
| NEXT e                  { next full $2 }
| PREV INTERVAL e         { prev $2 $3 }
| PREV e                  { prev full $2 }
| ONCE INTERVAL e         { once $2 $3 }
| ONCE e                  { once full $2 }
| HISTORICALLY INTERVAL e { historically $2 $3 }
| HISTORICALLY e          { historically full $2 }
| EVENTUALLY INTERVAL e   { eventually $2 $3 }
| EVENTUALLY e            { eventually full $2 }
| ALWAYS INTERVAL e       { always $2 $3 }
| ALWAYS e                { always full $2 }
