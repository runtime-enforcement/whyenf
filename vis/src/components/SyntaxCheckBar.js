import React, { useState } from 'react';
import Box from '@mui/material/Box';
import Stepper from '@mui/material/Stepper';
import Step from '@mui/material/Step';
import StepLabel from '@mui/material/StepButton';
import Button from '@mui/material/Button';
import Typography from '@mui/material/Typography';

const steps = ['Signature', 'Specification', 'Trace'];

export default function StatusBar() {
  const [checked, setChecked] = useState({});

  const completedSteps = () => {
    return Object.keys(checked).length;
  };

  return (
    <Box display="flex"
         justifyContent="center"
         alignItems="center"
         sx={{ width: '100%', height: '100%' }}>
      <Stepper activeStep={1}>
        {steps.map((label, index) => (
          <Step key={label} checked={checked[index]}>
            <StepLabel color="inherit">
              {label}
            </StepLabel>
          </Step>
        ))}
      </Stepper>
    </Box>
  );
}
