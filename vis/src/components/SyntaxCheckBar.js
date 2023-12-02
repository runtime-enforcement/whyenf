import React from 'react';
import Box from '@mui/material/Box';
import Stepper from '@mui/material/Stepper';
import Step from '@mui/material/Step';
import StepLabel from '@mui/material/StepButton';
import Typography from '@mui/material/Typography';

const steps = ['Signature', 'Formula', 'Trace'];

export default function StatusBar({ checkedInputs }) {

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
