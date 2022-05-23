import React from 'react';
import Grid from '@mui/material/Grid';
import Divider from '@mui/material/Divider';
import Box from '@mui/material/Box';
import Container from '@mui/material/Container';
import Card from '@mui/material/Card';
import CardContent from '@mui/material/CardContent';
import Typography from '@mui/material/Typography';
import Link from '@mui/material/Link';
import NNFLogo from './assets/nnf_logo.png';
import KULogo from './assets/ku_logo.png';

const card = (
  <React.Fragment>
    <CardContent>
      <Typography variant="body2">
        The <strong>Explanator2</strong> is an online monitoring tool that produces explanations for verdicts of
        Metric Temporal Logic formulas on arbitrary traces. <br />
        It is the successor of the <Link href="https://bitbucket.org/traytel/explanator/src/master/">Explanator</Link>.
      </Typography>
    </CardContent>
    <Box sx={{ mt: 2, mb: 4 }}>
      <Grid container
            justifyContent="center"
            alignItems="center"
            spacing={10}>
        <Grid item xs={9} sm={9} md={3} lg={3} xl={3}>
          <Box component="img"
               sx={{
                 maxWidth: 276,
                 maxHeight: 102,
               }}
               alt="University of Copenhagen's logo."
               src={KULogo}>
          </Box>
        </Grid>
        <Grid item xs={6} sm={6} md={3} lg={3} xl={3}>
          <Box component="img"
               sx={{
                 mt: { md: 4, lg: 4, xl: 4 },
                 maxWidth: 166,
                 maxHeight: 130,
               }}
               alt="Novo Nordisk foundations' logo."
               src={NNFLogo}>
          </Box>
        </Grid>
      </Grid>
    </Box>
  </React.Fragment>
);

export default function Help() {
  return (
    <Box style={{ height: '90vh', margin: 0, padding: 0 }}>
      <Container maxWidth={false}>
        <Box sx={{ mt: 11 }}>
          <Card variant="outlined">{card}</Card>
        </Box>
      </Container>
    </Box>
  );
}
