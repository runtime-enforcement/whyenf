import React, { useState, useEffect } from 'react';
import Box from '@mui/material/Box';
import TextField from '@mui/material/TextField';

export default function TraceTextField ({ trace, setTrace }) {

  const [localTrace, setLocalTrace] = useState("@0 a\n@3 a b\n@7\n@11 a\n@13 a\n@17 a\n@18 a b\n@18 a b\n@22 a\n@26 a\n@29 a\n@29\n@33 a\n@33 a\n@34 a\n@38 a b\n@41 a b\n@41 a\n@45 b\n@47 a\n@47 a\n@49 a\n@49 a\n@53 b\n@53 a b\n@56\n@56 a\n@60 a b\n@63 a\n@66 a b\n@67 a b\n@67 a\n@70 a b\n@72 a b\n@72 a b\n@73 a\n@77 a b");

  const handleChange = (event) => {
    setLocalTrace(event.target.value);
  };

  const handleBlur = (event) => {
    setTrace(event.target.value);
  };

  useEffect(() => {
    setTrace(localTrace);
  }, [trace]);

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
