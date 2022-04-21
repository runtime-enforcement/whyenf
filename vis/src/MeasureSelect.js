import React from 'react';
import Box from '@mui/material/Box';
import FormControl from '@mui/material/FormControl';
import InputLabel from '@mui/material/InputLabel';
import Select from '@mui/material/Select';
import MenuItem from '@mui/material/MenuItem';

export default function MeasureSelect ({ measure, setMeasure, fixParameters }) {

  const handleChange = (event) => {
    setMeasure(event.target.value);
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
      <FormControl fullWidth disabled={fixParameters}>
        <InputLabel id="measure-select-label">Measure</InputLabel>
        <Select
          labelId="measure-select-label"
          id="measure-select"
          value={measure}
          label="Measure"
          onChange={handleChange}
        >
          <MenuItem value={"size"}>Size</MenuItem>
          <MenuItem value={"minreach"}>Minimum reach</MenuItem>
          <MenuItem value={"maxreach"}>Maximum reach</MenuItem>
        </Select>
      </FormControl>
    </Box>
  );
}
