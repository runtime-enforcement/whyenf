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
open Db
%}

%token <string> DIGITS
%token <string> STRING
%token AT
%token LOPEN
%token ROPEN
%token COMMA
%token SEMICOLON
%token EOF

%start <Db.t> db
%%

db:
| AT DIGITS events EOF                   { db $2 $3 }

events:
| evts=separated_list (SEMICOLON, evt) { evts }

evt:
| STRING LOPEN consts ROPEN              { event $1 $3 }

consts:
| cs=separated_list (COMMA, STRING)      { cs }
