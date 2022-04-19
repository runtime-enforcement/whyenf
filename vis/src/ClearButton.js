import React from 'react';
import Box from '@mui/material/Box';
import Button from '@mui/material/Button';
import ClearIcon from '@mui/icons-material/Clear';

export default function ClearButton ({ handleClear }) {
  return (
    <Button
      variant="contained"
      size="large"
      color="error"
      sx={{
        width: '100%'
      }}
      onClick={handleClear}
    >
      <Box pt={1}>
        <ClearIcon color="inherit" />
      </Box>
    </Button>
  );
}
