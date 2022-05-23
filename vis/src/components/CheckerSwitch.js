import React, { useState, useEffect } from 'react';
import FormLabel from '@mui/material/FormLabel';
import FormControl from '@mui/material/FormControl';
import Switch from '@mui/material/Switch';
import Box from '@mui/material/Box';

export default function CheckerSwitch({ refresh, checker, setChecker }) {

  const [localChecker, setLocalChecker] = useState(false);

  const handleChange = () => {
    setLocalChecker(!localChecker);
  };

  useEffect(() => {
    if (refresh) {
      setChecker(localChecker);
    }
  });


  return (
    <Box sx={{ ml: 2 }}>
      <FormControl component="fieldset" variant="standard">
        <FormLabel component="legend">Verify</FormLabel>
          <Box sx={{ ml: -1 }}>
            <Switch checked={localChecker} onChange={handleChange} />
          </Box>
      </FormControl>
    </Box>
  );
}
