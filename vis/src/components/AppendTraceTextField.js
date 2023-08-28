import React, { useState, useEffect } from 'react';
import Box from '@mui/material/Box';
import TextField from '@mui/material/TextField';

export default function AppendTraceTextField ({ appendTrace, setAppendTrace }) {

  const [localTrace, setLocalTrace] = useState("");

  const handleChange = (event) => {
    setLocalTrace(event.target.value);
  };

  const handleBlur = (event) => {
    setAppendTrace(event.target.value);
  };

  useEffect(() => {
    setAppendTrace(localTrace);
  }, [appendTrace, localTrace, setAppendTrace]);

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
          multiline
          id="outlined-required"
          label="New events"
          value={localTrace}
          onChange={handleChange}
          onBlur={handleBlur}
        />
      </div>
    </Box>
  );
}
