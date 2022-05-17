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
    primary: {
      main: "#000000",
    },
    secondary: {
      main: "#6EB5FF",
    },
  },
});

function initMonitor(state, action) {
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
      ...state,
      dialog: translateError(error),
    };
  }
}

function execMonitor(state, action) {
  try {
    const monitor = window.monitorAppend(action.appendTrace,
                                         action.measure,
                                         action.formula,
                                         action.monitorState);
    const monitorState = monitor[1];
    const explanations = state.explanations.concat((JSON.parse(monitor[2])).expls);
    const atoms = state.atoms.concat((JSON.parse(monitor[2])).atoms);
    const squares = computeSquares(explanations, atoms);

    return { ...state,
             explanations: explanations,
             atoms: atoms,
             squares: squares,
             monitorState: monitorState,
             fixParameters: true
           };
  } catch (error) {
    console.log(error);
    return {
      ...state,
      dialog: translateError(error),
    };
  }
}

function reducer(state, action) {
  switch (action.type) {
  case 'initTable':
    return initMonitor(state, action);
  case 'appendTable':
    return execMonitor(state, action);
  case 'updateTable':
    return {
      ...state,
      squares: action.squares,
      selectedRows: action.selectedRows,
      highlightedCells: action.highlightedCells,
      fixParameters: true
    }
  case 'resetTable':
    return {
      ...state,
      squares: computeSquares(state.explanations, state.atoms),
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
      ...state,
      dialog: { name: action.name, message: action.message }
    }
  case 'closeDialog':
    return {
      ...state,
      dialog: {},
    }
  default:
    return state;
  }
}

function App() {
  const [measure, setMeasure] = useState("size");
  const [formula, setFormula] = useState("");
  const [trace, setTrace] = useState("@0 a\n@3 a b\n@7\n@11 a\n@13 a\n@17 a\n@18 a b\n@18 a b\n@22 a\n@26 a\n@29 a\n@29\n@33 a\n@33 a\n@34 a\n@38 a b\n@41 a b\n@41 a\n@45 b\n@47 a\n@47 a\n@49 a\n@49 a\n@53 b\n@53 a b\n@56\n@56 a\n@60 a b\n@63 a\n@66 a b\n@67 a b\n@67 a\n@70 a b\n@72 a b\n@72 a b\n@73 a\n@77 a b");
  const [appendTrace, setAppendTrace] = useState("");
  const [state, dispatch] = useReducer(reducer, { explanations: [],
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
                   formula: formula,
                   trace: trace,
                   type: 'initTable'
                 };

    dispatch(action);
  };

  const handleAppend = (e) => {
    e.preventDefault();

    let action;
    if (appendTrace === "") action = { type: 'openDialog',
                                       name: 'Error',
                                       message: 'Your trace is empty. Please try again.'
                                     };
    else action = { measure: measure,
                    formula: formula,
                    appendTrace: appendTrace,
                    monitorState: state.monitorState,
                    type: 'appendTable'
                  };

    dispatch(action);
  };

  const handleReset = (e) => {
    e.preventDefault();
    let action = { type: 'resetTable' };
    dispatch(action);
  }

  const handleLeave = (e) => {
    e.preventDefault();
    let action = { type: 'leaveMonitor' };
    dispatch(action);
  };

  return (
    <ThemeProvider theme={theme}>
      <Box>
        { (state.dialog !== undefined && (Object.keys(state.dialog).length !== 0)) &&
          <AlertDialog open={true} dialog={state.dialog} dispatch={dispatch} />
        }
        <NavBar />
        <Container maxWidth="xl">
          <Box sx={{ mb: 12 }}>
            <Grid container spacing={2}>
              <Grid item xs={12} sm={12} md={12} lg={12} xl={12}>
                <PreambleCard />
              </Grid>

              { !state.fixParameters &&
                <Grid item xs={12} sm={12} md={4} lg={4} xl={4}>
                  <MonitorButton handleMonitor={handleMonitor} />
                </Grid>
              }

              { state.fixParameters &&
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
                <FormulaTextField formula={formula}
                                  setFormula={setFormula}
                                  fixParameters={state.fixParameters}
                />
              </Grid>

              { !state.fixParameters &&
                <Grid container item xs={24} sm={24} md={12} lg={12} xl={12} spacing={2}>
                  <Grid item xs={12} sm={12} md={4} lg={4} xl={4}>
                    <TraceTextField trace={trace} setTrace={setTrace} />
                  </Grid>
                  <Grid item xs={12} sm={12} md={8} lg={8} xl={8}>
                    <TimeGrid explanations={state.explanations}
                              atoms={state.atoms}
                              apsColumns={state.apsColumns}
                              subfsColumns={state.subfsColumns}
                              squares={state.squares}
                              dispatch={dispatch}
                    />
                  </Grid>
                </Grid>
              }


              { state.fixParameters &&
                <Grid container item xs={24} sm={24} md={12} lg={12} xl={12} spacing={2}>
                  <Grid item xs={24} sm={24} md={12} lg={12} xl={12}>
                    <TimeGrid explanations={state.explanations}
                              atoms={state.atoms}
                              apsColumns={state.apsColumns}
                              subfsColumns={state.subfsColumns}
                              squares={state.squares}
                              selectedRows={state.selectedRows}
                              highlightedCells={state.highlightedCells}
                              dispatch={dispatch}
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
