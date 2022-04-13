import React, { useState, useEffect } from 'react';
import Box from '@mui/material/Box';
import TextField from '@mui/material/TextField';

export default function FormulaTextField ({ formula, setFormula }) {

  const [localFormula, setLocalFormula] = useState("(a SINCE b) SINCE (a SINCE b)");

  const handleChange = (event) => {
    setLocalFormula(event.target.value);
  };

  const handleBlur = (event) => {
    setFormula(event.target.value);
  };

  useEffect(() => {
    setFormula(localFormula);
  }, [formula]);

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
          required
          id="outlined-required"
          label="Formula"
          value={localFormula}
          onChange={handleChange}
          onBlur={handleBlur}
        />
      </div>
    </Box>
  );
}
