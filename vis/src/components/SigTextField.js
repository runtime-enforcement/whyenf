import React, { useState, useEffect } from 'react';
import Box from '@mui/material/Box';
import TextField from '@mui/material/TextField';

export default function SigTextField ({ sig, setFormState }) {

  const [localSig, setLocalSig] = useState("");
  const [rows, setRows] = useState(10);

  const ref = React.createRef();

  const handleChange = (event) => {
    setLocalSig(event.target.value);
  };

  const handleBlur = (event) => {
    setFormState({ type: 'setSig', sig: localSig });
  };

  useEffect(() => {
    setRows(ref.current.clientHeight/27.5);
    setLocalSig(sig);
  }, [sig, setLocalSig]);

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
        label="Signature"
        required
        multiline
        value={localSig}
        onChange={handleChange}
        onBlur={handleBlur}
        minRows={rows}
        maxRows={rows}
        InputProps={{style: { minHeight: '18vh',
                              maxHeight: '18vh',
                              fontSize: 14  } }}
      />
    </Box>
  );
}
