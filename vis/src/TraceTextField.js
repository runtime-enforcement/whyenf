import React from 'react';
import Box from '@mui/material/Box';
import TextField from '@mui/material/TextField';

export default class TraceTextField extends React.Component {
  render() {
    return (
      <Box
        component="form"
        sx={{
          '& .MuiTextField-root': { mt: 0, width: '100%' },
        }}
        noValidate
        autoComplete="off"
      >
        <TextField
          id="outlined-multiline-static"
          label="Trace"
          multiline
          rows={24}
          defaultValue="@0 b
@2 a
@2 a
@3 a b
@4 a
@10 a"
        />
      </Box>
    );
  }
}
