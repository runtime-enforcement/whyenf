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
import RandomExampleSelect from './RandomExampleSelect';
import ResetButton from './ResetButton';
import CheckerSwitch from './CheckerSwitch';
import PreambleCard from './PreambleCard';
import AlertDialog from './AlertDialog';
import { initSquares, translateError } from './util';

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

function init(action) {
  try {
    const m = JSON.parse(window.monitor(action.trace, action.checker, action.measure, action.formula)[2]);
    const e = m.expls;
    const a = m.atoms;
    const c = JSON.parse(window.getColumns(action.formula));
    const s = initSquares(e, a);

    return { explanations: e,
             atoms: a,
             apsColumns: c.apsColumns,
             subfsColumns: c.subfsColumns,
             squares: s,
             selectedRows: [],
             hideTrace: true
           };
  } catch (error) {
    return { explanations: [],
             atoms: [],
             apsColumns: [],
             subfsColumns: [],
             squares: [],
             selectedRows: [],
             dialog: translateError(error),
             hideTrace: false
           };
  }
}

function reducer(state, action) {
  switch (action.type) {
  case 'init':
    return init(action);
  case 'reset':
    return { explanations: state.explanations,
             atoms: state.atoms,
             apsColumns: state.apsColumns,
             subfsColumns: state.subfsColumns,
             squares: initSquares(state.explanations, state.atoms),
             selectedRows: [],
             hideTrace: true
           }
  case 'update':
    return { explanations: state.explanations,
             atoms: state.atoms,
             apsColumns: state.apsColumns,
             subfsColumns: state.subfsColumns,
             squares: action.squares,
             selectedRows: action.selectedRows,
             hideTrace: true
           }
  case 'openDialog':
    return { explanations: state.explanations,
             atoms: state.atoms,
             apsColumns: state.apsColumns,
             subfsColumns: state.subfsColumns,
             squares: state.squares,
             selectedRows: state.selectedRows,
             dialog: { type: action.dialogType, text: action.dialogText },
             hideTrace: state.hideTrace
           }
  case 'closeDialog':
    return { explanations: state.explanations,
             atoms: state.atoms,
             apsColumns: state.apsColumns,
             subfsColumns: state.subfsColumns,
             squares: state.squares,
             selectedRows: state.selectedRows,
             dialog: {},
             hideTrace: state.hideTrace
           }
  }
}

function App() {
  const [checker, setChecker] = useState(false);
  const [measure, setMeasure] = useState("size");
  const [formula, setFormula] = useState("(a SINCE b) SINCE (a SINCE b)");
  const [trace, setTrace] = useState("@0 a\n@3 a b\n@7\n@11 a\n@13 a\n@17 a\n@18 a b\n@18 a b\n@22 a\n@26 a\n@29 a\n@29\n@33 a\n@33 a\n@34 a\n@38 a b\n@41 a b\n@41 a\n@45 b\n@47 a\n@47 a\n@49 a\n@49 a\n@53 b\n@53 a b\n@56\n@56 a\n@60 a b\n@63 a\n@66 a b\n@67 a b\n@67 a\n@70 a b\n@72 a b\n@72 a b\n@73 a\n@77 a b");
  const [appendTrace, setAppendTrace] = useState("");
  const [state, dispatch] = useReducer(reducer, { explanations: [],
                                                  atoms: [],
                                                  apsColumns: [],
                                                  subfsColumns: [],
                                                  squares: [],
                                                  selectedRows: [],
                                                  dialog: {},
                                                  hideTrace: false
                                                });

  const handleRefresh = (e) => {
    e.preventDefault();

    let action;
    if (state.measure === measure && state.formula === formula && state.trace === trace) action = { type: 'reset' };
    else action = {
      checker: false,
      measure: measure,
      formula: formula,
      trace: trace,
      type: 'init'
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
        <Container maxWidth="lg">
          <Box sx={{ mb: 12 }}>
            <Grid container spacing={2}>
              <Grid item xs={12} sm={12} md={12} lg={12} xl={12}>
                <PreambleCard />
              </Grid>
              <Grid item xs={11} sm={11} md={4} lg={4} xl={4}>
                <RefreshButton handleRefresh={handleRefresh} />
              </Grid>
              <Grid item xs={12} sm={12} md={1.5} lg={1.5} xl={1.5}>
                <MeasureSelect measure={measure} setMeasure={setMeasure} />
              </Grid>
              <Grid item xs={12} sm={12} md={6.5} lg={6.5} xl={6.5}>
                <FormulaTextField formula={formula} setFormula={setFormula} />
              </Grid>

              { !state.hideTrace &&
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


              { state.hideTrace &&
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
