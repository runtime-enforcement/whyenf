import React from 'react';
import OutlinedInput from '@mui/material/OutlinedInput';
import InputLabel from '@mui/material/InputLabel';
import MenuItem from '@mui/material/MenuItem';
import FormControl from '@mui/material/FormControl';
import ListItemText from '@mui/material/ListItemText';
import Select from '@mui/material/Select';
import Checkbox from '@mui/material/Checkbox';

const options = [
  'Trace',
  'Unix Timestamps',
];

export default function CheckmarkOptions({ selectedOptions, setMonitorState }) {

  let optionArray = [...selectedOptions];

  const handleChange = (event) => {
    const {
      target: { value },
    } = event;

    let action = { type: "updateOptions",
                   options: value };
    setMonitorState(action);
  };

  return (
    <div>
      <FormControl sx={{ width: '100%' }}>
        <InputLabel id="checkmark-options-label">Options</InputLabel>
        <Select
          labelId="checkmark-options-label"
          id="checkmark-options"
          multiple
          value={optionArray}
          onChange={handleChange}
          input={<OutlinedInput label="Options" />}
          renderValue={(selected) => selected.join(', ')}
        >
          {options.map((name) => (
            <MenuItem key={name} value={name}>
              <Checkbox checked={[...selectedOptions].indexOf(name) > -1}/>
              <ListItemText primary={name} />
            </MenuItem>
          ))}
        </Select>
      </FormControl>
    </div>
  );
}
