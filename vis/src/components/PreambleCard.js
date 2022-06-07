import * as React from 'react';
import Box from '@mui/material/Box';
import Card from '@mui/material/Card';
import CardContent from '@mui/material/CardContent';
import Typography from '@mui/material/Typography';
import { Link } from 'react-router-dom';

const card = (
  <React.Fragment>
    <CardContent>
      <Typography variant="h6">
        Welcome to the Explanator2
      </Typography>
      <Typography variant="body2">
        This is a tool for online monitoring satisfaction and violation verdicts
        of Metric Temporal Logic formulas on arbitrary traces. <br />
        For more details, click <Link to="/about" style={{ color: '#977b01' }}>here</Link>.
      </Typography>
    </CardContent>
  </React.Fragment>
);

export default function PreambleCard() {
  return (
    <Box sx={{ mt: 11 }}>
      <Card variant="outlined">{card}</Card>
    </Box>
  );
}
