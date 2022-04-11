import React from 'react';
import Box from '@mui/material/Box';
import Button from '@mui/material/Button';
import RefreshIcon from '@mui/icons-material/Refresh';

export default function RefreshButton ({ handleRefresh }) {
  return (
    <Button
      variant="contained"
      size="large"
      sx={{
        width: '100%'
      }}
      onClick={handleRefresh}
    >
      <Box pt={1}>
        <RefreshIcon color="inherit" />
      </Box>
    </Button>
  );
}
