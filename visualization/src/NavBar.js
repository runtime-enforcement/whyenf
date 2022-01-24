import * as React from 'react';
import AppBar from '@mui/material/AppBar';
import Box from '@mui/material/Box';
import Toolbar from '@mui/material/Toolbar';
import Typography from '@mui/material/Typography';
import Button from '@mui/material/Button';
import HelpIcon from '@mui/icons-material/Help';
import InfoIcon from '@mui/icons-material/Info';

export default function NavBar() {
  return (
    <Box sx={{ flexGrow: 1 }}>
      <AppBar position="fixed">
        <Toolbar>
          <Typography variant="h6" component="div" sx={{ flexGrow: 1 }}>
            eXpLaNaToR
          </Typography>
          <Button color="inherit">
            <HelpIcon color="inherit" sx={{ mr: 0.5 }} /> help
          </Button>
          <Button color="inherit">
            <InfoIcon color="inherit" sx={{ mr: 0.5 }} /> about
          </Button>
    </Toolbar>
    </AppBar>
    </Box>
  );
}
