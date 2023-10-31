import React, { useState, useEffect } from 'react';
import Box from '@mui/material/Box';
import Stepper from '@mui/material/Stepper';
import Step from '@mui/material/Step';
import StepLabel from '@mui/material/StepButton';
import Button from '@mui/material/Button';
import Typography from '@mui/material/Typography';

const steps = ['Signature', 'Formula', 'Trace'];

export default function StatusBar({ checkedInputs }) {
  const [activeStep, setActiveStep] = React.useState(0);

  const totalSteps = () => {
    return steps.length;
  };

  const checkedSteps = () => {
    return Object.keys(checkedInputs).length;
  };

  const isLastStep = () => {
    return activeStep === totalSteps() - 1;
  };

  const allStepsChecked = () => {
    return checkedSteps() === totalSteps();
  };

  const handleNext = () => {
    const newActiveStep =
      isLastStep() && !allStepsChecked()
        ? steps.findIndex((step, i) => !(i in checkedInputs))
        : activeStep + 1;
    setActiveStep(newActiveStep);
  };

  return (
    <Box display="flex"
         justifyContent="center"
         alignItems="center"
         sx={{ width: '100%', height: '100%' }}>
      <Stepper nonLinear>
        {steps.map((label, index) => (
          <Step active expanded key={label} completed={checkedInputs[index]}>
            <StepLabel color="inherit">
              {label}
            </StepLabel>
          </Step>
        ))}
      </Stepper>
    </Box>
  );
}
