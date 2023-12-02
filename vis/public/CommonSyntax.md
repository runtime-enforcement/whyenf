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

{UPPERBOUND} ::=   {NAT}
                 | INFINITY (∞)

{I}  ::=   [{NAT}, {NAT}]
         | [{NAT}, {UPPERBOUND})
```