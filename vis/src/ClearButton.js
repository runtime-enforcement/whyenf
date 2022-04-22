import React from 'react';
import Box from '@mui/material/Box';
import Button from '@mui/material/Button'
import ClearAllIcon from '@mui/icons-material/ClearAll';

export default function ClearButton ({ handleClear }) {
  return (
    <Button
      variant="contained"
      size="large"
      color="error"
      onClick={handleClear}
      fullWidth
    >
      <Box pt={1}>
        <ClearAllIcon color="inherit" />
      </Box>
    </Button>
  );
}
