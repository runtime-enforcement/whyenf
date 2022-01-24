import * as React from 'react';
import FormControlLabel from '@mui/material/FormControlLabel';
import Switch from '@mui/material/Switch';
import Box from '@mui/material/Box';

export default function CheckerSwitch() {
  return (
    <Box sx={{ ml: 1, mt: 2 }}>
      <FormControlLabel control={<Switch />} label="Verified Checker" />
    </Box>
  );
}
