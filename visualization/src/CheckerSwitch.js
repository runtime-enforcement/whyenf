import * as React from 'react';
import FormGroup from '@mui/material/FormGroup';
import FormControlLabel from '@mui/material/FormControlLabel';
import Switch from '@mui/material/Switch';
import Box from '@mui/material/Box';

export default function CheckerSwitch() {
  return (
    <Box sx={{ mt: 4 }}>
      <FormControlLabel control={<Switch />} label="Verified Checker" />
    </Box>
  );
}
