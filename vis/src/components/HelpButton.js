import React from 'react';
import Button from '@mui/material/Button';
import QuestionMarkIcon from '@mui/icons-material/QuestionMark';

export default function HelpButton ({ isHelpCardVisible, setIsHelpCardVisible }) {

  return (
    <Button
      variant="contained"
      size="large"
      color="warning"
      sx={{ width: '100%', height: '100%' }}
      onClick={() => setIsHelpCardVisible(!isHelpCardVisible)}
    >
      <QuestionMarkIcon/>
    </Button>
  );
}
