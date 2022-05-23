import React from "react";
import Box from '@mui/material/Box';
import { ThemeProvider, createTheme } from '@mui/material/styles';
import NavBar from './NavBar';
import Monitor from './Monitor';

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

function App() {
  return (
    <ThemeProvider theme={theme}>
      <Box>
        <NavBar />
        <Monitor />
      </Box>
    </ThemeProvider>
  );
}

export default App;
