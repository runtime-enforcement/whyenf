import React, { useState, useEffect } from 'react';
import Box from '@mui/material/Box';
import TextField from '@mui/material/TextField';

export default function TraceTextField ({ trace, setFormState }) {

  const [localTrace, setLocalTrace] = useState(trace);

  const handleChange = (event) => {
    setLocalTrace(event.target.value);
  };

  const handleBlur = (event) => {
    setFormState({ type: 'setTrace', trace: localTrace });
  };

  useEffect(() => {
    setLocalTrace(trace);
  }, [trace, setLocalTrace]);

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
        required
        multiline
        value={localTrace}
        onChange={handleChange}
        onBlur={handleBlur}
        minRows={22}
        maxRows={22}
        InputProps={{style: { minHeight: '65vh' }}}
      />
    </Box>
  );
}
