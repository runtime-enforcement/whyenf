import React from 'react';
import Box from '@mui/material/Box';
import TextField from '@mui/material/TextField';

export default function FormulaTextField ({ formula, setFormula }) {

  const handleChange = (event) => {
    setFormula(event.target.value);
  };

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
          value={formula}
          onChange={handleChange}
        />
      </div>
    </Box>
  );
}
