import React from 'react';
import Box from '@mui/material/Box';
import TextField from '@mui/material/TextField';

export default function TraceTextField ({ trace, setTrace }) {

  const handleChange = (event) => {
    setTrace(event.target.value);
  };

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
        value={trace}
        onChange={handleChange}
      />
    </Box>
  );
}
