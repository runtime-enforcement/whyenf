import * as React from 'react';
import Box from '@mui/material/Box';
import Card from '@mui/material/Card';
import CardActions from '@mui/material/CardActions';
import CardContent from '@mui/material/CardContent';
import Button from '@mui/material/Button';
import Typography from '@mui/material/Typography';
import Link from '@mui/material/Link';

const bull = (
  <Box
    component="span"
    sx={{ display: 'inline-block', mx: '2px', transform: 'scale(0.8)' }}
  >
    •
  </Box>
);

const card = (
  <React.Fragment>
    <CardContent>
      <Typography variant="h5" component="div">
        Explanator2: Judgement Day
      </Typography>
      <Typography sx={{ mt: 3 }} variant="body2">
        This is a tool for online monitoring satisfaction and violation explanations
        of MTL (Metric Temporal Logic) formulas on arbitrary traces. <br />
        It is built upon the <Link href="https://bitbucket.org/traytel/explanator/src/master/">Explanator</Link>.
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
