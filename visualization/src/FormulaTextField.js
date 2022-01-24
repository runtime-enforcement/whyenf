import React from 'react';
import Box from '@mui/material/Box';
import TextField from '@mui/material/TextField';

export default class FormulaTextField extends React.Component {
  render() {
    return (
      <Box
        component="form"
        sx={{
          '& .MuiTextField-root': { mt: 4, width: '100%' },
        }}
        noValidate
        autoComplete="off"
      >
        <div>
          <TextField
            required
            id="outlined-required"
            label="Formula"
            defaultValue="a1 S[2,4] a2"
          />
        </div>
      </Box>
    );
  }
}
