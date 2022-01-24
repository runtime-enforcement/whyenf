import React from 'react';
import Box from '@mui/material/Box';
import TextField from '@mui/material/TextField';
import Button from '@mui/material/Button';
import RefreshIcon from '@mui/icons-material/Refresh';

export default class RefreshButton extends React.Component {
  render() {
    return (
      <Box
        component="form"
        sx={{ mt: 2 }}
        noValidate
        autoComplete="off"
      >
        <Button
          variant="contained"
          size="large"
          sx={{
            width: '35.3ch'
          }}
        >
          <Box pr={1} pt={1}>
            <RefreshIcon color="action" />
          </Box>
          Refresh
        </Button>
      </Box>
    );
  }
}
