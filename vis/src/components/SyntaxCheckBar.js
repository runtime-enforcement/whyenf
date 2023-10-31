import React, { useState, useEffect } from 'react';
import Box from '@mui/material/Box';
import Stepper from '@mui/material/Stepper';
import Step from '@mui/material/Step';
import StepLabel from '@mui/material/StepButton';
import Button from '@mui/material/Button';
import Typography from '@mui/material/Typography';
import CancelIcon from '@mui/icons-material/Cancel';

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
        {steps.map((label, index) => {
          const labelProps = {};
          if (checkedInputs[index]) {
            labelProps.optional = (
              <Typography variant="caption" color="#388e3c">
                valid
              </Typography>
            );
          }

          return (
            <Step active={!checkedInputs[index]} expanded
                  key={label}
                  completed={checkedInputs[index]}
                  sx={{
                    '& .MuiStepLabel-root .Mui-completed': {
                      color: 'black', // circle's color
                    },
                    '& .MuiStepLabel-label.Mui-completed.MuiStepLabel-alternativeLabel':
                    {
                      color: 'black',
                    },
                    '& .MuiStepLabel-root .Mui-active': {
                      color: 'black', // circle's color
                    },
                    '& .MuiStepLabel-label.Mui-active.MuiStepLabel-alternativeLabel':
                    {
                      color: 'common.white',
                    },
                    '& .MuiStepLabel-root .Mui-active .MuiStepIcon-text': {
                      fill: 'black', // circle's number
                    },
                  }}>
              <StepLabel {...labelProps}>
                {label}
              </StepLabel>
            </Step>
          );
        })}
      </Stepper>
    </Box>
  );
}
