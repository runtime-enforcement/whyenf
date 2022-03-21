import React, { useState, useEffect } from "react";
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

function App() {
  const [checker, setChecker] = useState(false);
  const [measure, setMeasure] = useState("size");
  const [formula, setFormula] = useState("a SINCE b");
  const [trace, setTrace] = useState("@0 b\n@2 a\n@2 a\n@3 a b\n@4 a\n@10 a");

  return (
    <ThemeProvider theme={theme}>
      <Box>
        <NavBar />
        <Container maxWidth="lg">
          <Box sx={{ mb: 12 }}>
            <Grid container spacing={2}>
              <Grid item xs={12} sm={12} md={12} lg={12} xl={12}>
                <PreambleCard />
              </Grid>
              <Grid item xs={6} sm={6} md={2} lg={2} xl={2}>
                <RefreshButton />
              </Grid>
              <Grid item xs={3} sm={3} md={1} lg={1} xl={1}>
                <ResetButton />
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
                <TimeGrid checker={checker}
                          measure={measure}
                          formula={formula}
                          trace={trace}
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
