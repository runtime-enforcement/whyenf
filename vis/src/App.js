import React, { useState, useReducer } from "react";
import Grid from '@mui/material/Grid';
import Box from '@mui/material/Box';
import Container from '@mui/material/Container';
import { ThemeProvider, createTheme } from '@mui/material/styles';
import TraceTextField from './TraceTextField';
import FormulaTextField from './FormulaTextField';
import MeasureSelect from './MeasureSelect';
import NavBar from './NavBar';
import BottomBar from './BottomBar';
import TimeGrid from './TimeGrid';
import RefreshButton from './RefreshButton';
import RandomExampleButton from './RandomExampleButton';
import ResetButton from './ResetButton';
import CheckerSwitch from './CheckerSwitch';
import PreambleCard from './PreambleCard';
import ErrorDialog from './ErrorDialog';
import { initSquares } from './util';

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
    const c = JSON.parse(window.getColumns(action.formula)).columns;
    const s = initSquares(e, a);
    return { explanations: e, atoms: a, columns: c, squares: s };
  } catch (error) {
    console.error(error);
    return { explanations: [], atoms: [], columns: [], squares: [] };
  }
}

function reducer(state, action) {
  switch (action.type) {
  case 'init':
    return init(action);
  case 'reset':
    return { explanations: state.explanations,
             atoms: state.atoms,
             columns: state.columns,
             squares: initSquares(state.explanations)
           }
  case 'update':
    return { explanations: state.explanations,
             atoms: state.atoms,
             columns: state.columns,
             squares: action.squares
           }
  }
}

function App() {
  const [checker, setChecker] = useState(false);
  const [measure, setMeasure] = useState("size");
  const [formula, setFormula] = useState("(a SINCE b) SINCE (a SINCE b)");
  const [trace, setTrace] = useState("@0 a\n@3 a b\n@7\n@11 a\n@13 a\n@17 a\n@18 a b\n@18 a b\n@22 a\n@26 a\n@29 a\n@29\n@33 a\n@33 a\n@34 a\n@38 a b\n@41 a b\n@41 a\n@45 b\n@47 a\n@47 a\n@49 a\n@49 a\n@53 b\n@53 a b\n@56\n@56 a\n@60 a b\n@63 a\n@66 a b\n@67 a b\n@67 a\n@70 a b\n@72 a b\n@72 a b\n@73 a\n@77 a b");
  const [state, dispatch] = useReducer(reducer, { explanations: [], atoms: [], columns: [], squares: [] });
  const [errorDialog, setErrorDialog] = useState({ open: false, error: "" });

  const handleRefresh = (e) => {
    e.preventDefault();
    let action = {
      checker: checker,
      measure: measure,
      formula: formula,
      trace: trace,
      type: 'init'
    };
    dispatch(action);
  };

  const handleReset = (e) => {
    e.preventDefault();
    let action = { type: 'reset' };
    dispatch(action);
  };

  return (
    <ThemeProvider theme={theme}>
      <Box>
        { errorDialog.open && <ErrorDialog errorDialog={errorDialog} setErrorDialog={setErrorDialog} /> }
        <NavBar />
        <Container maxWidth="lg">
          <Box sx={{ mb: 12 }}>
            <Grid container spacing={2}>
              <Grid item xs={12} sm={12} md={12} lg={12} xl={12}>
                <PreambleCard />
              </Grid>
              <Grid item xs={6} sm={6} md={2} lg={2} xl={2}>
                <RefreshButton handleRefresh={handleRefresh} />
              </Grid>
              <Grid item xs={3} sm={3} md={1} lg={1} xl={1}>
                <ResetButton handleReset={handleReset} />
              </Grid>
              <Grid item xs={2} sm={2} md={1} lg={1} xl={1}>
                <CheckerSwitch checker={checker} setChecker={setChecker} />
              </Grid>
              <Grid item xs={12} sm={12} md={1.5} lg={1.5} xl={1.5}>
                <MeasureSelect measure={measure} setMeasure={setMeasure} />
              </Grid>
              <Grid item xs={12} sm={12} md={6.5} lg={6.5} xl={6.5}>
                <FormulaTextField formula={formula} setFormula={setFormula} />
              </Grid>
              <Grid item xs={12} sm={12} md={4} lg={4} xl={4}>
                <TraceTextField trace={trace} setTrace={setTrace} />
              </Grid>
              <Grid item xs={12} sm={12} md={8} lg={8} xl={8}>
                <TimeGrid explanations={state.explanations}
                          columns={state.columns}
                          squares={state.squares}
                          dispatch={dispatch}
                />
              </Grid>
            </Grid>
          </Box>
        </Container>
        <BottomBar />
      </Box>
    </ThemeProvider>
  );
}

export default App;
