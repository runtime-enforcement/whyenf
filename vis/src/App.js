import React, { useState, useReducer } from "react";
import Grid from '@mui/material/Grid';
import Box from '@mui/material/Box';
import Container from '@mui/material/Container';
import { ThemeProvider, createTheme } from '@mui/material/styles';
import TraceTextField from './TraceTextField';
import AppendTraceTextField from './AppendTraceTextField';
import FormulaTextField from './FormulaTextField';
import NavBar from './NavBar';
import TimeGrid from './TimeGrid';
import MonitorButton from './MonitorButton';
import AppendButton from './AppendButton';
import LeaveButton from './LeaveButton';
import ResetButton from './ResetButton';
import ExampleSelect from './ExampleSelect';
import PreambleCard from './PreambleCard';
import AlertDialog from './AlertDialog';
import { computeSquares, translateError } from './util';

const theme = createTheme({
  palette: {
    type: 'light',
    primary: {
      main: '#222222',
    },
    secondary: {
      main: '#fdd835',
    },
  },
});

function initMonitor(monitorState, action) {
  try {
    const monitor = window.monitorInit(action.trace, action.measure, action.formula);
    const monitorState = monitor[1];
    const explanations = (JSON.parse(monitor[2])).expls;
    const atoms = (JSON.parse(monitor[2])).atoms;
    const columns = JSON.parse(window.getColumns(action.formula));
    const squares = computeSquares(explanations, atoms);

    return { explanations: explanations,
             atoms: atoms,
             apsColumns: columns.apsColumns,
             subfsColumns: columns.subfsColumns,
             squares: squares,
             monitorState: monitorState,
             selectedRows: [],
             highlightedCells: [],
             fixParameters: true
           };
  } catch (error) {
    console.log(error);
    return {
      ...monitorState,
      dialog: translateError(error),
    };
  }
}

function execMonitor(monitorState, action) {
  try {
    const monitor = window.monitorAppend(action.appendTrace,
                                         action.measure,
                                         action.formula,
                                         action.monitorState);
    const monitorState = monitor[1];
    const explanations = monitorState.explanations.concat((JSON.parse(monitor[2])).expls);
    const atoms = monitorState.atoms.concat((JSON.parse(monitor[2])).atoms);
    const squares = computeSquares(explanations, atoms);

    return { ...monitorState,
             explanations: explanations,
             atoms: atoms,
             squares: squares,
             monitorState: monitorState,
             fixParameters: true
           };
  } catch (error) {
    console.log(error);
    return {
      ...monitorState,
      dialog: translateError(error),
    };
  }
}

function formStateReducer(formState, action) {
  switch (action.type) {
  case 'setFormula':
    return {
      ...formState,
      formula: action.formula
    }
  case 'setTrace':
    return {
      ...formState,
      trace: action.trace
    }
  case 'setFormulaAndTrace':
    return {
      formula: action.formula,
      trace: action.trace
    }
  default:
    return formState;
  }
}

function monitorStateReducer(monitorState, action) {
  switch (action.type) {
  case 'initTable':
    return initMonitor(monitorState, action);
  case 'appendTable':
    return execMonitor(monitorState, action);
  case 'updateTable':
    return {
      ...monitorState,
      squares: action.squares,
      selectedRows: action.selectedRows,
      highlightedCells: action.highlightedCells,
      fixParameters: true
    }
  case 'resetTable':
    return {
      ...monitorState,
      squares: computeSquares(monitorState.explanations, monitorState.atoms),
      selectedRows: [],
      highlightedCells: [],
      fixParameters: true
    }
  case 'leaveMonitor':
    return { explanations: [],
             atoms: [],
             apsColumns: [],
             subfsColumns: [],
             squares: [],
             monitorState: [],
             selectedRows: [],
             highlightedCells: [],
             dialog: {},
             fixParameters: false
           }
  case 'openDialog':
    return {
      ...monitorState,
      dialog: { name: action.name, message: action.message }
    }
  case 'closeDialog':
    return {
      ...monitorState,
      dialog: {},
    }
  default:
    return monitorState;
  }
}

function App() {
  const [measure, setMeasure] = useState("size");
  const [appendTrace, setAppendTrace] = useState("");
  const [formState, setFormState] = useReducer(formStateReducer, { formula: "", trace: "" });
  const [monitorState, setMonitorState] = useReducer(monitorStateReducer,
                                              { explanations: [],
                                                atoms: [],
                                                apsColumns: [],
                                                subfsColumns: [],
                                                squares: [],
                                                monitorState: [],
                                                selectedRows: [],
                                                highlightedCells: [],
                                                dialog: {},
                                                fixParameters: false
                                              });

  const handleMonitor = (e) => {
    e.preventDefault();

    let action = { measure: measure,
                   formula: formState.formula,
                   trace: formState.trace,
                   type: 'initTable'
                 };

    setMonitorState(action);
  };

  const handleAppend = (e) => {
    e.preventDefault();

    let action;
    if (appendTrace === "") action = { type: 'openDialog',
                                       name: 'Error',
                                       message: 'Your trace is empty. Please try again.'
                                     };
    else action = { measure: measure,
                    formula: formState.formula,
                    appendTrace: appendTrace,
                    monitorState: monitorState.monitorState,
                    type: 'appendTable'
                  };

    setMonitorState(action);
  };

  const handleReset = (e) => {
    e.preventDefault();
    let action = { type: 'resetTable' };
    setMonitorState(action);
  }

  const handleLeave = (e) => {
    e.preventDefault();
    let action = { type: 'leaveMonitor' };
    setMonitorState(action);
  };

  return (
    <ThemeProvider theme={theme}>
      <Box>
        { (monitorState.dialog !== undefined && (Object.keys(monitorState.dialog).length !== 0)) &&
          <AlertDialog open={true} dialog={monitorState.dialog} setMonitorState={setMonitorState} />
        }
        <NavBar />
        <Container maxWidth="xl">
          <Box sx={{ mb: 12 }}>
            <Grid container spacing={2}>
              <Grid item xs={12} sm={12} md={12} lg={12} xl={12}>
                <PreambleCard />
              </Grid>

              { !monitorState.fixParameters &&
                <Grid container item xs={12} sm={12} md={4} lg={4} xl={4} spacing={2}>
                  <Grid item xs={12} sm={12} md={6} lg={6} xl={6}>
                    <ExampleSelect setFormState={setFormState} />
                  </Grid>
                  <Grid item xs={12} sm={12} md={6} lg={6} xl={6}>
                    <MonitorButton handleMonitor={handleMonitor} />
                  </Grid>
                </Grid>
              }

              { monitorState.fixParameters &&
                <Grid container item xs={12} sm={12} md={4} lg={4} xl={4} spacing={2}>
                  <Grid item xs={12} sm={12} md={6} lg={6} xl={6}>
                    <AppendTraceTextField appendTrace={appendTrace} setAppendTrace={setAppendTrace} />
                  </Grid>
                  <Grid item xs={12} sm={12} md={2} lg={2} xl={2}>
                    <AppendButton handleAppend={handleAppend} />
                  </Grid>
                  <Grid item xs={12} sm={12} md={2} lg={2} xl={2}>
                    <ResetButton handleReset={handleReset} />
                  </Grid>
                  <Grid item xs={12} sm={12} md={2} lg={2} xl={2}>
                    <LeaveButton handleLeave={handleLeave} />
                  </Grid>
                </Grid>
              }

              <Grid item xs={12} sm={12} md={8} lg={8} xl={8}>
                <FormulaTextField formula={formState.formula}
                                  setFormState={setFormState}
                                  fixParameters={monitorState.fixParameters}
                />
              </Grid>

              { !monitorState.fixParameters &&
                <Grid container item xs={24} sm={24} md={12} lg={12} xl={12} spacing={2}>
                  <Grid item xs={12} sm={12} md={4} lg={4} xl={4}>
                    <TraceTextField trace={formState.trace} setFormState={setFormState} />
                  </Grid>
                  <Grid item xs={12} sm={12} md={8} lg={8} xl={8}>
                    <TimeGrid explanations={monitorState.explanations}
                              atoms={monitorState.atoms}
                              apsColumns={monitorState.apsColumns}
                              subfsColumns={monitorState.subfsColumns}
                              squares={monitorState.squares}
                              setMonitorState={setMonitorState}
                    />
                  </Grid>
                </Grid>
              }


              { monitorState.fixParameters &&
                <Grid container item xs={24} sm={24} md={12} lg={12} xl={12} spacing={2}>
                  <Grid item xs={24} sm={24} md={12} lg={12} xl={12}>
                    <TimeGrid explanations={monitorState.explanations}
                              atoms={monitorState.atoms}
                              apsColumns={monitorState.apsColumns}
                              subfsColumns={monitorState.subfsColumns}
                              squares={monitorState.squares}
                              selectedRows={monitorState.selectedRows}
                              highlightedCells={monitorState.highlightedCells}
                              setMonitorState={setMonitorState}
                    />
                  </Grid>
                </Grid>
              }

            </Grid>
          </Box>
        </Container>
      </Box>
    </ThemeProvider>
  );
}

export default App;
