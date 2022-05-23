import React from 'react';
import Box from '@mui/material/Box';
import Button from '@mui/material/Button';
import AddIcon from '@mui/icons-material/Add';

export default function AppendButton ({ handleAppend }) {
  return (
    <Button
      variant="contained"
      size="large"
      sx={{
        width: '100%'
      }}
      onClick={handleAppend}
    >
      <Box pt={1}>
        <AddIcon color="inherit" />
      </Box>
    </Button>
  );
}
