import React from 'react';
import Box from '@mui/material/Box';
import FormControl from '@mui/material/FormControl';
import InputLabel from '@mui/material/InputLabel';
import Select from '@mui/material/Select';
import MenuItem from '@mui/material/MenuItem';

export default function ExampleSelect ({ example, setExample }) {

  const handleChange = (event) => {
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
      <FormControl fullWidth>
        <Select
          labelId="example-select-label"
          id="example-select"
          label="Ex"
          value={example}
          onChange={handleChange}
        >
          <MenuItem value={"intrusion-detection"}>Intrusion Detection</MenuItem>
        </Select>
      </FormControl>
    </Box>
  );
}
