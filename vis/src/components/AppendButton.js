import React from 'react';
import Box from '@mui/material/Box';
import Button from '@mui/material/Button';
import AddIcon from '@mui/icons-material/Add';
import Zoom from '@mui/material/Zoom';
import { black } from '../util';

export default function AppendButton ({ handleAppend, BootstrapTooltip }) {
  return (
    <BootstrapTooltip title="Add new events"
                      placement="top"
                      TransitionComponent={Zoom}>
      <Button
        color="secondary"
        variant="contained"
        size="large"
        sx={{ width: '100%' }}
        style={{ color: black }}
        onClick={handleAppend}
      >
        <Box pt={1}>
          <AddIcon color="inherit" />
        </Box>
      </Button>
    </BootstrapTooltip>
  );
}
