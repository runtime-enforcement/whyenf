import React from 'react';
import Box from '@mui/material/Box';
import Button from '@mui/material/Button';
import DeleteSweepIcon from '@mui/icons-material/DeleteSweep';

export default function ClearButton ({ handleClear }) {
  return (
    <Button
      variant="contained"
      size="large"
      sx={{
        width: '100%'
      }}
      onClick={handleClear}
    >
      <Box pt={1}>
        <DeleteSweepIcon color="inherit" />
      </Box>
    </Button>
  );
}
