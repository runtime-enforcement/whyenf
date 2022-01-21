import React from 'react';
import Box from '@mui/material/Box';
import TextField from '@mui/material/TextField';
import MenuItem from '@mui/material/MenuItem';

const measures = [
  {
    value: "size",
    label: "Size",
  },
  {
    value: "reach",
    label: "Reach",
  }
]

export default class MeasureSelect extends React.Component {
  render() {
    return (
      <Box
        component="form"
        sx={{
          '& .MuiTextField-root': { m: 1, width: '50ch' },
        }}
        noValidate
        autoComplete="off"
      >
        <div>
          <TextField
            id="outlined-select-measure"
            select
            label="Select Measure"
            helperText="MeasureSelect helper text"
          >
            {measures.map((option) => (
              <MenuItem key={option.value} value={option.value}>
                {option.label}
              </MenuItem>
            ))}
          </TextField>
        </div>
      </Box>
    );
  }
}
