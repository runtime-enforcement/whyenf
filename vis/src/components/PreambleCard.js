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
        An online monitor of Metric First-Order Temporal Logic specifications on arbitrary traces.
      </Typography>
    </CardContent>
  </React.Fragment>
);

export default function PreambleCard() {
  return (
    <Box sx={{ mt: 11 }}>
      <Card variant="outlined" style={{ border: "none", boxShadow: "none" }}>{card}</Card>
    </Box>
  );
}
