# Help

Welcome! To start, you can select one of the predefined examples using the dropdown menu.

Alternatively, you can specify your own Metric First-Order Temporal Logic formula, trace and signature. The syntax is the following:

### Metric First-Order Temporal Logic
```
{PRED} ::= string

{VAR} ::= string

{VARS} ::=   {VAR}
           | {VAR}, {VARS}

{CONST} ::= quoted string

{I}  ::= [{NAT}, {UPPERBOUND}]

{UPPERBOUND} ::=   {NAT}
                 | INFINITY   (∞)

{f} ::=   {PRED}({VARS})
        | true                  (⊤)
        | false                 (⊥)
        | {VAR} EQCONST {CONST} (=)
        | NOT {f}               (¬)
        | {f} AND {f}           (∧)
        | {f} OR  {f}           (∨)
        | {f} IMPLIES {f}       (→)
        | {f} IFF {f}           (↔)
        | EXISTS {VAR}. {f}     (∃)
        | FORALL {VAR}. {f}     {∀}
        | PREV{I} {f}           (●)
        | NEXT{I} {f}           (○)
        | ONCE{I} {f}           (⧫)
        | EVENTUALLY{I} {f}     (◊)
        | HISTORICALLY{I} {f}   (■)
        | ALWAYS{I} {f}         (□)
        | {f} SINCE{I} {f}      (S)
        | {f} UNTIL{I} {f}      (U)
        | {f} TRIGGER{I} {f}    (T)
        | {f} RELEASE{I} {f}    (R)
```

Note that this tool also supports the equivalent Unicode characters (on the right).

### Signature
```
{TYPE} ::= string | int

{VARTYPES} ::=   {VAR}:{TYPE}
               | {VAR}:{TYPE}, {VARTYPES}

{SIG} ::=   {PRED}({VARTYPES})
          | {PRED}({VARTYPES}) \n {SIG}
```

### Trace
```
{TRACE} :=   @{NAT} {PREDICATE}(VALUES)*
           | @{NAT} {PREDICATE}()* \n {TRACE}
```