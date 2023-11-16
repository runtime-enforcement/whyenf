import React from 'react';
import Box from '@mui/material/Box';
import Button from '@mui/material/Button';
import ClearIcon from '@mui/icons-material/Clear';
import { black } from '../util';

export default function LeaveButton ({ handleLeave, BootstrapTooltip }) {
  return (
    <BootstrapTooltip title="Exit">
      <Button
        variant="contained"
        size="large"
        color="error"
        sx={{ width: '100%' }}
        style={{ color: black }}
        onClick={handleLeave}
      >
        <Box pt={1}>
          <ClearIcon color={black} />
        </Box>
      </Button>
    </BootstrapTooltip>
  );
}
