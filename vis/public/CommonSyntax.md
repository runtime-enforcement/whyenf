```
{CONST} ::= quoted string

{PRED} ::= string

{VAR} ::= string

{VARS} ::=   {VAR}
           | {VAR}, {VARS}

{VARORCONSTS} ::=   {VAR}
                  | {CONST}
                  | {VAR}, {VARORCONSTS}
                  | {CONST}, {VARORCONSTS}

{I}  ::= [{NAT}, {UPPERBOUND}]

{UPPERBOUND} ::=   {NAT}
                 | INFINITY (∞)
```