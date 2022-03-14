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
          defaultValue="@0 a
@3 a b
@7
@11 a
@13 a
@17 a
@18 a b
@18 a b
@22 a
@26 a
@29 a
@29
@33 a
@33 a
@34 a
@38 a b
@41 a b
@41 a
@45 b
@47 a
@47 a
@49 a
@49 a
@53 b
@53 a b
@56
@56 a
@60 a b
@63 a
@66 a b
@67 a b
@67 a
@70 a b
@72 a b
@72 a b
@73 a
@77 a b"
        />
      </Box>
    );
  }
}
