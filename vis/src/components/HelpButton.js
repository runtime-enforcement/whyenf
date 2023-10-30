import React from 'react';
import Box from '@mui/material/Box';
import Button from '@mui/material/Button';
import QuestionMarkIcon from '@mui/icons-material/QuestionMark';

export default function HelpButton ({ handleMonitor }) {
  return (
    <Button
      variant="contained"
      size="large"
      color="secondary"
      sx={{ width: '100%', height: '100%' }}
      onClick={handleMonitor}
    >
      <QuestionMarkIcon/>
    </Button>
  );
}
