# Help

To start, you can select one of the predefined examples using the dropdown menu.

Alternatively, you can write your own Metric Temporal Logic specification and trace. The syntax is the following:

### Metric Temporal Logic
```
{f} ::=   true
        | false
        | {ATOM}
        | NOT {f}
        | {f} AND {f}
        | {f} OR  {f}
        | {f} IFF {f}
        | {f} IMPLIES {f}
        | PREV{i} {f}
        | NEXT{i} {f}
        | ONCE{i} {f}
        | EVENTUALLY{i} {f}
        | HISTORICALLY{i} {f}
        | ALWAYS{i} {f}
        | {f} SINCE{i} {f}
        | {f} UNTIL{i} {f}
        | {f} TRIGGER{i} {f}
        | {f} RELEASE{i} {f}

{i}  ::= [{NAT}, {UPPERBOUND}]
{UPPERBOUND} ::= {NAT} | INFINITY
```

### Trace
```
{TRACE} :=   @{NAT} {ATOM}*
           | @{NAT} {ATOM}* \n {TRACE}
```

Once you have a valid MTL formula and trace, you can run the monitor by clicking on the monitoring button:

<img alt="Monitoring button" src="./assets/monitoring_button.png" width="15%" height="15%" style="margin:0px 25px" />
