import React from 'react';
import Box from '@mui/material/Box';
import Button from '@mui/material/Button';
import MonitorIcon from '@mui/icons-material/Monitor';
import { black } from '../util';

export default function MonitorButton ({ handleMonitor }) {
  return (
    <Button
      color="secondary"
      variant="contained"
      endIcon={<MonitorIcon color="primary"/>}
      size="large"
      sx={{ width: '100%', height: '100%'}}
      style={{ color: black }}
      onClick={handleMonitor}
    >
      Run
    </Button>
  );
}
