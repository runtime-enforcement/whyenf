import React from 'react';
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
  return (
    <ThemeProvider theme={theme}>
      <Box>
        <NavBar />
        <Container maxWidth="lg">
          <Box>
            <Grid container spacing={2}>
              <Grid item xs={12} sm={12} md={12} lg={12} xl={12}>
                <PreambleCard />
              </Grid>
              <Grid item xs={3} sm={3} md={1.5} lg={1.5} xl={1.5}>
                <RefreshButton />
              </Grid>
              <Grid item xs={3} sm={3} md={1} lg={1} xl={1}>
                <RandomExampleButton />
              </Grid>
              <Grid item xs={6} sm={6} md={1.5} lg={1.5} xl={1.5}>
                <CheckerSwitch />
              </Grid>
              <Grid item xs={12} sm={12} md={1.5} lg={1.5} xl={1.5}>
                <MeasureSelect />
              </Grid>
              <Grid item xs={12} sm={12} md={6.5} lg={6.5} xl={6.5}>
                <FormulaTextField />
              </Grid>
              <Grid item xs={12} sm={12} md={4} lg={4} xl={4}>
                <TraceTextField />
              </Grid>
              <Grid item xs={12} sm={12} md={8} lg={8} xl={8}>
                <TimeGrid />
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
