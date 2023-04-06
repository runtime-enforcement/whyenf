/*******************************************************************
 *     This is part of Explanator2, it is distributed under the    *
 *     terms of the GNU Lesser General Public License version 3    *
 *           (see file LICENSE for more details)                   *
 *                                                                 *
 *  Copyright 2023:                                                *
 *  Dmitriy Traytel (UCPH)                                         *
 *  Leonardo Lima (UCPH)                                           *
 *******************************************************************/

%token <string> STRING
%token LOPEN
%token ROPEN
%token COMMA
%token COLON
%token EOF

%start <Pred.Sig.t> sig_pred
%%

sig_pred:
| STRING LOPEN ntconsts ROPEN            { Pred.Sig.sig_pred $1 $3 }

ntconsts:
| ntcs=separated_list (COMMA, ntconst)   { ntcs }

ntconst:
| STRING COLON STRING                    { Pred.Sig.ntconst $1 $3 }
