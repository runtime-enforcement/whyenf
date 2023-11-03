import React, { useState, useEffect, createRef } from 'react';
import Box from '@mui/material/Box';
import TextField from '@mui/material/TextField';

export default function AppendTraceTextField ({ appendTrace, setAppendTrace }) {
  const [localTrace, setLocalTrace] = useState("");
  const [rows, setRows] = useState(12);

  const ref = createRef();

  const handleChange = (event) => {
    setLocalTrace(event.target.value);
  };

  const handleBlur = (event) => {
    setAppendTrace(event.target.value);
  };

  useEffect(() => {
    setRows(ref.current.clientHeight/25);
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
      ref={ref}
    >
      <div>
        <TextField
          multiline
          id="outlined-required"
          label="New events"
          value={localTrace}
          onChange={handleChange}
          onBlur={handleBlur}
          minRows={rows}
          maxRows={rows}
          InputProps={{style: { minHeight: '16vh',
                                maxHeight: '16vh',
                                fontSize: 14
                              }
                      }}
        />
      </div>
    </Box>
  );
}
