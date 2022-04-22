import * as React from 'react';
import AppBar from '@mui/material/AppBar';
import Box from '@mui/material/Box';
import Toolbar from '@mui/material/Toolbar';
import Typography from '@mui/material/Typography';
import IconButton from '@mui/material/IconButton';
import GitHubIcon from '@mui/icons-material/GitHub';
import TwitterIcon from '@mui/icons-material/Twitter';

export default function BottomBar() {
  return (
    <Box sx={{ mb: 0, flexGrow: 4, width: '100%', bottom: 0, position: 'fixed' }}>
      <AppBar position="static">
        <Toolbar>
          <Typography align="center" variant="h8" component="div" sx={{ flexGrow: 1 }}>
            <IconButton
              size="large"
              edge="start"
              color="inherit"
              aria-label="menu"
              sx={{ mr: 2 }}
            >
              <GitHubIcon />
            </IconButton>
            <IconButton
              size="large"
              edge="start"
              color="inherit"
              aria-label="menu"
              sx={{ mr: 2 }}
            >
              <TwitterIcon />
            </IconButton>
          </Typography>
        </Toolbar>
      </AppBar>
    </Box>
  );
}
