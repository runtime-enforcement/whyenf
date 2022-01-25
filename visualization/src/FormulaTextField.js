import React from 'react';
import Box from '@mui/material/Box';
import TextField from '@mui/material/TextField';

export default class FormulaTextField extends React.Component {
  render() {
    return (
      <Box
        component="form"
        sx={{
          '& .MuiTextField-root': { width: '100%' },
        }}
        noValidate
        autoComplete="off"
      >
        <div>
          <TextField
            required
            id="outlined-required"
            label="Formula"
            defaultValue="(NOT a1) SINCE[4,8] a2"
          />
        </div>
      </Box>
    );
  }
}
