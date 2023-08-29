import React, { useState, useEffect } from 'react';
import Box from '@mui/material/Box';
import TextField from '@mui/material/TextField';

export default function TraceTextField ({ trace, setFormState }) {

  const [localTrace, setLocalTrace] = useState("");
  const [rows, setRows] = useState(10);

  const ref = React.createRef();

  const handleChange = (event) => {
    setLocalTrace(event.target.value);
  };

  const handleBlur = (event) => {
    setFormState({ type: 'setTrace', trace: localTrace });
  };

  useEffect(() => {
    setRows(ref.current.clientHeight/22.5);
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
      ref={ref}
    >
      <TextField
        id="outlined-multiline-static"
        label="Trace"
        required
        multiline
        value={localTrace}
        onChange={handleChange}
        onBlur={handleBlur}
        minRows={rows}
        maxRows={rows}
        InputProps={{ style: { minHeight: '40vh',
                               fontSize: 14 } }}
      />
    </Box>
  );
}
