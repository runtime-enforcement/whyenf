import React from 'react';
import Grid from '@mui/material/Grid';
import Box from '@mui/material/Box';
import Container from '@mui/material/Container';
import logo from './logo.svg';
import './App.css';
import TraceTextField from './TraceTextField';
import FormulaTextField from './FormulaTextField';
import MeasureSelect from './MeasureSelect';
import AppBar from './AppBar';
import TimeGrid from './TimeGrid';
import RefreshButton from './RefreshButton';
import CheckerSwitch from './CheckerSwitch';

function App() {
  return (
    <Box>
      <AppBar />
      <Container maxWidth="lg">
        <Box>
          <Grid container spacing={2}>
            <Grid item xs={6} sm={6} md={2.5} lg={2.5} xl={2.5}>
              <MeasureSelect />
            </Grid>
            <Grid item xs={6} sm={6} md={1.5} lg={1.5} xl={1.5}>
              <CheckerSwitch />
            </Grid>
            <Grid item xs={12} sm={12} md={8} lg={8} xl={8}>
              <FormulaTextField />
            </Grid>
            <Grid item xs={12} sm={12} md={4} lg={4} xl={4}>
              <RefreshButton />
              <TraceTextField />
            </Grid>
            <Grid item xs={12} sm={12} md={8} lg={8} xl={8}>
              <TimeGrid />
            </Grid>
          </Grid>
        </Box>
      </Container>
    </Box>
  );
}

export default App;
