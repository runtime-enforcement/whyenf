import React from 'react';
import Box from '@mui/material/Box';
import TextField from '@mui/material/TextField';

export default function AppendTraceTextField ({ appendTrace, setAppendTrace }) {

  const handleChange = (event) => {
    setAppendTrace(event.target.value);
  };

  return (
    <Box
      component="form"
      sx={{
        '& .MuiTextField-root': { width: '100%' },
      }}
      noValidate
      autoComplete="off"
    >
      <TextField
        id="outlined-multiline-static"
        label="Trace"
        multiline
        rows={2}
        value={appendTrace}
        onChange={handleChange}
      />
    </Box>
  );
}
