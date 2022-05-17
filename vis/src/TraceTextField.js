import React, { useState, useEffect } from 'react';
import Box from '@mui/material/Box';
import TextField from '@mui/material/TextField';

export default function TraceTextField ({ trace, setTrace }) {

  const [localTrace, setLocalTrace] = useState(trace);

  const handleChange = (event) => {
    setLocalTrace(event.target.value);
  };

  const handleBlur = (event) => {
    setTrace(event.target.value);
  };

  useEffect(() => {
    setTrace(localTrace);
  }, [localTrace, setTrace]);

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
        rows={24}
        value={localTrace}
        onChange={handleChange}
        onBlur={handleBlur}
      />
    </Box>
  );
}
