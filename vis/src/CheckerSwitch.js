import * as React from 'react';
import FormLabel from '@mui/material/FormLabel';
import FormControl from '@mui/material/FormControl';
import FormControlLabel from '@mui/material/FormControlLabel';
import Switch from '@mui/material/Switch';
import Box from '@mui/material/Box';

export default function CheckerSwitch({ checker, setChecker }) {

  const handleChange = () => {
    checker = !checker;
    console.log(checker);
    setChecker(checker);
  };

  return (
    <Box sx={{ ml: 2 }}>
      <FormControl component="fieldset" variant="standard">
        <FormLabel component="legend">Verify</FormLabel>
          <Box sx={{ ml: -1 }}>
            <Switch checked={checker} onChange={handleChange} />
          </Box>
      </FormControl>
    </Box>
  );
}
