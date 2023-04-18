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

%start <Pred.Sig.t> pred_sig
%%

pred_sig:
| STRING LOPEN n_tts ROPEN EOF           { Pred.Sig.make $1 $3 }

n_tts:
| ntts=separated_list (COMMA, n_tt)      { ntts }

n_tt:
| STRING COLON STRING                    { Pred.Sig.n_tt $1 $3 }
