import React from 'react';
import Box from '@mui/material/Box';
import Button from '@mui/material/Button';
import RefreshIcon from '@mui/icons-material/Refresh';

export default function ResetButton ({ handleReset }) {
  return (
    <Button
      variant="contained"
      size="large"
      color="secondary"
      sx={{
        width: '100%'
      }}
      onClick={handleReset}
    >
      <Box pt={1}>
        <RefreshIcon color="inherit" />
      </Box>
    </Button>
  );
}
