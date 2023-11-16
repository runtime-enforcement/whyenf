import React from 'react';
import Box from '@mui/material/Box';
import Button from '@mui/material/Button';
import UndoIcon from '@mui/icons-material/Undo';
import { black } from '../util';

export default function UndoButton ({ handleUndo }) {
  return (
    <Button
      variant="contained"
      size="large"
      sx={{ width: '100%' }}
      style={{ color: black, backgroundColor: '#FFCE81' }}
      onClick={handleUndo}
    >
      <Box pt={1}>
        <UndoIcon color={black} />
      </Box>
    </Button>
  );
}
