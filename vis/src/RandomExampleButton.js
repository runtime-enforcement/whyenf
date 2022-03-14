import React from 'react';
import Box from '@mui/material/Box';
import Button from '@mui/material/Button';
import ShuffleIcon from '@mui/icons-material/Shuffle';

export default class RandomExampleButton extends React.Component {
  render() {
    return (
        <Button
          variant="contained"
          size="large"
          sx={{
            width: '100%'
          }}
        >
          <Box pt={1}>
            <ShuffleIcon color="inherit" />
          </Box>
        </Button>
    );
  }
}
