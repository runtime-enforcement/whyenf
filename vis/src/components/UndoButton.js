import React from 'react';
import Box from '@mui/material/Box';
import Button from '@mui/material/Button';
import UndoIcon from '@mui/icons-material/Undo';
import Zoom from '@mui/material/Zoom';
import { black } from '../util';

export default function UndoButton ({ handleUndo, BootstrapTooltip }) {
  return (
    <BootstrapTooltip title="Undo (not implemented yet)"
                      placement="top"
                      TransitionComponent={Zoom}>
      <Button
        variant="contained"
        size="large"
        sx={{ width: '100%' }}
        style={{ color: black, backgroundColor: '#FFCE81' }}
        /* onClick={handleUndo} */
      >
        <Box pt={1}>
          <UndoIcon color={black} />
        </Box>
      </Button>
    </BootstrapTooltip>
  );
}
