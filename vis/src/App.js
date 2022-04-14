import React, { useState, useReducer } from "react";
import Grid from '@mui/material/Grid';
import Box from '@mui/material/Box';
import Container from '@mui/material/Container';
import { ThemeProvider, createTheme } from '@mui/material/styles';
import TraceTextField from './TraceTextField';
import AppendTraceTextField from './AppendTraceTextField';
import FormulaTextField from './FormulaTextField';
import MeasureSelect from './MeasureSelect';
import NavBar from './NavBar';
import BottomBar from './BottomBar';
import TimeGrid from './TimeGrid';
import RefreshButton from './RefreshButton';
import AppendButton from './AppendButton';
import ClearButton from './ClearButton';
import RandomExampleSelect from './RandomExampleSelect';
import PreambleCard from './PreambleCard';
import AlertDialog from './AlertDialog';
import { computeSquares, translateError } from './util';

const theme = createTheme({
  palette: {
    primary: {
      main: "#000000",
    },
    secondary: {
      main: "#39ff14",
    },
  },
});

function execMonitor(state, action) {
  try {
    const monitor = window.monitorInit(action.trace, action.checker, action.measure, action.formula);
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
             fixParameters: true
           };
  } catch (error) {
    return {
      ...state,
      dialog: translateError(error),
    };
  }
}

function reducer(state, action) {
  switch (action.type) {
  case 'init':
    return execMonitor(state, action);
  case 'reset':
    return {
      ...state,
      squares: computeSquares(state.explanations, state.atoms),
      selectedRows: [],
      fixParameters: true
    }
  case 'update':
    return {
      ...state,
      squares: action.squares,
      selectedRows: action.selectedRows,
      fixParameters: true
    }
  case 'openDialog':
    return {
      ...state,
      dialog: { type: action.dialogType, text: action.dialogText }
    }
  case 'closeDialog':
    return {
      ...state,
      dialog: {},
    }
  }
}

function App() {
  const [checker, setChecker] = useState(false);
  const [measure, setMeasure] = useState("size");
  const [formula, setFormula] = useState("");
  const [trace, setTrace] = useState("");
  const [appendTrace, setAppendTrace] = useState("");
  const [state, dispatch] = useReducer(reducer, { explanations: [],
                                                  atoms: [],
                                                  apsColumns: [],
                                                  subfsColumns: [],
                                                  squares: [],
                                                  monitorState: [],
                                                  selectedRows: [],
                                                  dialog: {},
                                                  fixParameters: false,
                                                  lockFormulaAndMeasure: false
                                                });

  const handleRefresh = (e) => {
    e.preventDefault();

    let action;
    if (state.measure === measure && state.formula === formula && state.trace === trace) action = { type: 'reset' };
    else action = { checker: checker,
                    measure: measure,
                    formula: formula,
                    trace: trace,
                    type: 'init'
                  };

    dispatch(action);
  };

  const handleAppend = (e) => {
    e.preventDefault();

    let action;
    if (appendTrace === "") return;
    else action = { checker: checker,
                    measure: measure,
                    formula: formula,
                    trace: trace,
                    type: 'append'
                  };

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
                  <RefreshButton handleRefresh={handleRefresh} />
                </Grid>
              }

              { state.fixParameters &&
                <Grid container item xs={12} sm={12} md={4} lg={4} xl={4} spacing={2}>
                  <Grid item xs={12} sm={12} md={8} lg={8} xl={8}>
                    <RefreshButton handleRefresh={handleRefresh} />
                  </Grid>
                  <Grid item xs={12} sm={12} md={2} lg={2} xl={2}>
                    <AppendButton handleRefresh={handleRefresh} />
                  </Grid>
                  <Grid item xs={12} sm={12} md={2} lg={2} xl={2}>
                    <ClearButton handleRefresh={handleRefresh} />
                  </Grid>
                </Grid>
              }

              <Grid item xs={12} sm={12} md={1.5} lg={1.5} xl={1.5}>
                <MeasureSelect measure={measure} setMeasure={setMeasure} />
              </Grid>
              <Grid item xs={12} sm={12} md={6.5} lg={6.5} xl={6.5}>
                <FormulaTextField formula={formula} setFormula={setFormula} />
              </Grid>

              { !state.fixParameters &&
                <Grid container item xs={24} sm={24} md={12} lg={12} xl={12} spacing={2}>
                  <Grid item xs={12} sm={12} md={4} lg={4} xl={4}>
                    <TraceTextField trace={trace} setTrace={setTrace} />
                  </Grid>
                  <Grid item xs={12} sm={12} md={8} lg={8} xl={8}>
                    <TimeGrid explanations={state.explanations}
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
                              apsColumns={state.apsColumns}
                              subfsColumns={state.subfsColumns}
                              squares={state.squares}
                              selectedRows={state.selectedRows}
                              dispatch={dispatch}
                    />
                  </Grid>
                  <Grid item xs={12} sm={12} md={4} lg={4} xl={4}>
                    <AppendTraceTextField appendTrace={appendTrace} setAppendTrace={setAppendTrace} />
                  </Grid>
                </Grid>
              }

            </Grid>
          </Box>
        </Container>
        <BottomBar />
      </Box>
    </ThemeProvider>
  );
}

export default App;
