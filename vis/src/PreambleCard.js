import * as React from 'react';
import Box from '@mui/material/Box';
import Card from '@mui/material/Card';
import CardContent from '@mui/material/CardContent';
import Typography from '@mui/material/Typography';
import Link from '@mui/material/Link';

const card = (
  <React.Fragment>
    <CardContent>
      <Typography variant="body2">
        This is a tool for online monitoring satisfaction and violation explanations
        of MTL (Metric Temporal Logic) formulas on arbitrary traces. <br />
        It is the successor of the <Link href="https://bitbucket.org/traytel/explanator/src/master/">Explanator</Link>.
      </Typography>
    </CardContent>
  </React.Fragment>
);

export default function PreambleCard() {
  return (
    <Box sx={{ mt: 12, minWidth: 275 }}>
      <Card variant="outlined">{card}</Card>
    </Box>
  );
}
