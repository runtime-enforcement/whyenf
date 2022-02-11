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
            <Typography variant="h7" component="div" sx={{ flexGrow: 1 }}>
              help
            </Typography>
          </Button>
          <Button color="inherit">
            <Typography variant="h7" component="div" sx={{ flexGrow: 1 }}>
              about
            </Typography>
          </Button>
    </Toolbar>
    </AppBar>
    </Box>
  );
}
