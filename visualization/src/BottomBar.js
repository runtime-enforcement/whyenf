import * as React from 'react';
import AppBar from '@mui/material/AppBar';
import Box from '@mui/material/Box';
import Toolbar from '@mui/material/Toolbar';
import Typography from '@mui/material/Typography';
import Button from '@mui/material/Button';
import IconButton from '@mui/material/IconButton';
import MenuIcon from '@mui/icons-material/Menu';

export default function BottomBar() {
  return (
    <Box sx={{ mt: 4, flexGrow: 1 }}>
      <AppBar position="static">
        <Toolbar>
          <Typography variant="h8" component="div" sx={{ flexGrow: 1 }}>
            All rights reserved.
          </Typography>
        </Toolbar>
      </AppBar>
    </Box>
  );
}
