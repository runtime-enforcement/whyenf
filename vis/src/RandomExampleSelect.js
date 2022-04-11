import React from 'react';
import Box from '@mui/material/Box';
import FormControl from '@mui/material/FormControl';
import InputLabel from '@mui/material/InputLabel';
import Select from '@mui/material/Select';
import MenuItem from '@mui/material/MenuItem';

export default function RandomExampleSelect ({ example, setExample }) {

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
        <InputLabel id="random-example-select-label">Measure</InputLabel>
        <Select
          labelId="random-example-select-label"
          id="random-example-select"
          value={example}
          label="Example"
          onChange={handleChange}
        >
          <MenuItem value={"example1"}>Example1</MenuItem>
        </Select>
      </FormControl>
    </Box>
  );
}
