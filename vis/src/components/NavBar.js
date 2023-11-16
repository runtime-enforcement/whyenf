import * as React from 'react';
import AppBar from '@mui/material/AppBar';
import Box from '@mui/material/Box';
import Toolbar from '@mui/material/Toolbar';
import Typography from '@mui/material/Typography';
import Button from '@mui/material/Button';
import OfflineBoltIcon from '@mui/icons-material/OfflineBolt';
import InfoIcon from '@mui/icons-material/Info';
import BugReportIcon from '@mui/icons-material/BugReport';
import { Link } from 'react-router-dom';

export default function NavBar() {
  return (
    <Box sx={{ flexGrow: 1 }}>
      <AppBar position="fixed">
        <Toolbar>
          <Typography variant="h5" component="div" sx={{ flexGrow: 1 }}>
            <Link to="/" style={{ textDecoration: 'none' }}>
              <Button color="secondary">
                <Typography variant="h6" component="div">
                  WhyMon
                </Typography>
              </Button>
            </Link>
          </Typography>
          <Link to="/quickstart" style={{ textDecoration: 'none' }}>
            <Button color="secondary" startIcon={<OfflineBoltIcon />}>
              <Typography variant="button" component="div" >
                Quickstart
              </Typography>
            </Button>
          </Link>
          <a href="https://github.com/runtime-monitoring/whymon/issues" target="_blank" rel="noreferrer" style={{ textDecoration: 'none' }}>
            <Button color="secondary" startIcon={<BugReportIcon />}>
              <Typography variant="button" component="div" >
                Report a bug
              </Typography>
            </Button>
          </a>
          <Link to="/about" style={{ textDecoration: 'none' }}>
            <Button color="secondary" startIcon={<InfoIcon />}>
              <Typography variant="button" component="div">
              About
              </Typography>
            </Button>
          </Link>
    </Toolbar>
    </AppBar>
    </Box>
  );
}
