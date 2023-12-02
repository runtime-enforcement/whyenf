import React from 'react';
import Box from '@mui/material/Box';
import Button from '@mui/material/Button';
import RefreshIcon from '@mui/icons-material/Refresh';
import Zoom from '@mui/material/Zoom';

export default function ResetButton ({ handleReset, BootstrapTooltip }) {
  return (
    <BootstrapTooltip title="Reset"
                      placement="top"
                      TransitionComponent={Zoom}>
      <Button
        variant="contained"
        size="large"
        color="warning"
        sx={{
          width: '100%'
        }}
        onClick={handleReset}
      >
        <Box pt={1}>
          <RefreshIcon color="inherit" />
        </Box>
      </Button>
    </BootstrapTooltip>
  );
}
