import React from 'react';
import Box from '@mui/material/Box';
import TextField from '@mui/material/TextField';
import Button from '@mui/material/Button';
import RefreshIcon from '@mui/icons-material/Refresh';

export default class TraceBox extends React.Component {
  render() {
    return (
      <form>
        <Box
          component="form"
          sx={{
            '& .MuiTextField-root': { m: 1, width: '50ch' },
          }}
          noValidate
          autoComplete="off"
        >
          <div>
            <TextField
              id="outlined-multiline-static"
              label="Trace"
              multiline
              rows={12}
              defaultValue="@0 a1 a2..."
            />
          </div>
        </Box>
        <Button
          variant="contained"
          size="large"
          sx={{
            width: '50ch'
          }}
        >
          <RefreshIcon color="action" />
          Update grid
        </Button>
      </form>
    );
  }
}
