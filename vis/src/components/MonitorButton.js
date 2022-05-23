import React from 'react';
import Box from '@mui/material/Box';
import Button from '@mui/material/Button';
import MonitorIcon from '@mui/icons-material/Monitor';

export default function MonitorButton ({ handleMonitor }) {
  return (
    <Button
      variant="contained"
      size="large"
      sx={{
        width: '100%'
      }}
      onClick={handleMonitor}
    >
      <Box pt={1}>
        <MonitorIcon color="inherit" />
      </Box>
    </Button>
  );
}
