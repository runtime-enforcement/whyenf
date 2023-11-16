import React from 'react';
import Box from '@mui/material/Box';
import Button from '@mui/material/Button';
import MonitorIcon from '@mui/icons-material/Monitor';

export default function MonitorButton ({ handleMonitor }) {
  return (
    <Button
      color="secondary"
      variant="contained"
      endIcon={<MonitorIcon color="inherit"/>}
      size="large"
      sx={{ width: '100%', height: '100%' }}
      onClick={handleMonitor}
    >
      Run
    </Button>
  );
}
