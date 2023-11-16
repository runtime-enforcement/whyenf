```
{VALUES} ::=   int
             | string
             | int, {VALUES}
             | string, {VALUES}

{TRACE} ::=   @{NAT} {PRED}(VALUES)*
            | @{NAT} {PRED}()* \n {TRACE}
```