import React from 'react';
import Box from '@mui/material/Box';
import TextField from '@mui/material/TextField';

export default class TraceTextField extends React.Component {
  render() {
    return (
      <Box
        component="form"
        sx={{
          '& .MuiTextField-root': { mt: 3, width: '100%' },
        }}
        noValidate
        autoComplete="off"
      >
        <TextField
          id="outlined-multiline-static"
          label="Trace"
          multiline
          rows={23}
          defaultValue="@0 a
@3 a b
@7
@11 a
@13 a"
        />
      </Box>
    );
  }
}
