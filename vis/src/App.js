import React from "react";
import Box from '@mui/material/Box';
import { ThemeProvider, createTheme } from '@mui/material/styles';
import { BrowserRouter, Routes, Route } from 'react-router-dom';
import NavBar from './components/NavBar';
import Monitor from './Monitor';
import Quickstart from './Quickstart';
import About from './About';

const theme = createTheme({
  palette: {
    mode: 'light',
    primary: {
      main: '#222222',
    },
    secondary: {
      main: '#3e999f',
    },
    warning: {
      main: '#f5871f',
    },
  },
});

function App() {
  return (
    <ThemeProvider theme={theme}>
      <Box>
        <BrowserRouter basename="/whymon">
          <NavBar />
          <Routes>
            <Route path="/" element={<Monitor />} />
            <Route path="/quickstart" element={<Quickstart />} />
            <Route path="/about" element={<About />} />
          </Routes>
        </BrowserRouter>
      </Box>
    </ThemeProvider>
  );
}

export default App;
