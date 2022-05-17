import React, { useState } from 'react';
import Box from '@mui/material/Box';
import FormControl from '@mui/material/FormControl';
import Select from '@mui/material/Select';
import MenuItem from '@mui/material/MenuItem';

export default function ExampleSelect ({ setTrace, setFormula }) {

  const [example, setExample] = useState("");

  const handleChange = (event) => {
    console.log(event.target.value);
    setExample(event.target.value);
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
        <FormControl fullWidth>
          <Select
            id="example-select"
            label="Example"
            value={example}
            onChange={handleChange}
          >
            <MenuItem value={"intrusion-detection"}>Intrusion Detection</MenuItem>
          </Select>
        </FormControl>
      </div>
    </Box>
  );
}
