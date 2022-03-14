import React from 'react';
import Box from '@mui/material/Box';
import Button from '@mui/material/Button'
import ClearAllIcon from '@mui/icons-material/ClearAll';

export default class ResetButton extends React.Component {
  render() {
    return (
        <Button
          variant="contained"
          size="large"
          sx={{
            width: '100%'
          }}
        >
          <Box pt={1}>
            <ClearAllIcon color="inherit" />
          </Box>
        </Button>
    );
  }
}
