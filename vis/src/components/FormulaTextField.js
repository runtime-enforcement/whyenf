import React, { useState, useEffect } from 'react';
import Box from '@mui/material/Box';
import TextField from '@mui/material/TextField';

export default function FormulaTextField ({ formula, setFormState, fixParameters }) {

  const [localFormula, setLocalFormula] = useState("");

  const handleChange = (event) => {
    setLocalFormula(event.target.value);
  };

  const handleBlur = (event) => {
    setFormState({ type: 'setFormula', formula: localFormula });
  };

  useEffect(() => {
    setLocalFormula(formula);
  }, [formula, setLocalFormula]);

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
          disabled={fixParameters}
        />
      </div>
    </Box>
  );
}
