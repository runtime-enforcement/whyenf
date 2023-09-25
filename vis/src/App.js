import React from "react";
import Box from '@mui/material/Box';
import { ThemeProvider, createTheme } from '@mui/material/styles';
import { BrowserRouter, Routes, Route } from 'react-router-dom';
import NavBar from './components/NavBar';
import Monitor from './Monitor';
import Help from './Help';
import About from './About';

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
        <BrowserRouter basename="/whymon">
          <NavBar />
          <Routes>
            <Route path="/" element={<Monitor />} />
            <Route path="/help" element={<Help />} />
            <Route path="/about" element={<About />} />
          </Routes>
        </BrowserRouter>
      </Box>
    </ThemeProvider>
  );
}

export default App;
