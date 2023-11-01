import React, { useState, useEffect } from 'react';
import PropTypes from 'prop-types';
import Tabs from '@mui/material/Tabs';
import Tab from '@mui/material/Tab';
import Typography from '@mui/material/Typography';
import Box from '@mui/material/Box';
import Card from '@mui/material/Card';
import CardContent from '@mui/material/CardContent';
import Divider from '@mui/material/Divider';
import Button from '@mui/material/Button';
import CloseIcon from '@mui/icons-material/Close';
import ReactMarkdown from 'react-markdown';
import rehypeRaw from 'rehype-raw';

function CustomTabPanel(props) {
  const { children, value, index, ...other } = props;

  return (
    <div
      role="tabpanel"
      hidden={value !== index}
      id={`simple-tabpanel-${index}`}
      aria-labelledby={`simple-tab-${index}`}
      {...other}
    >
      {value === index && (
        <Box sx={{ p: 3 }}>
          <Typography>{children}</Typography>
        </Box>
      )}
    </div>
  );
}

CustomTabPanel.propTypes = {
  children: PropTypes.node,
  index: PropTypes.number.isRequired,
  value: PropTypes.number.isRequired,
};

function propses(index) {
  return {
    id: `simple-tab-${index}`,
    'aria-controls': `simple-tabpanel-${index}`,
  };
}

export default function HelpCard({ setIsHelpCardVisible }) {
  const [value, setValue] = useState(0);
  const [sigSyntax, setSigSyntax] = useState("");
  const [formulaSyntax, setFormulaSyntax] = useState("");
  const [traceSyntax, setTraceSyntax] = useState("");
  const [commonSyntax, setCommonSyntax] = useState("");

  const handleChange = (event, newValue) => {
    setValue(newValue);
  };

  useEffect(() => {
    fetch("CommonSyntax.md")
      .then((res) => res.text())
      .then((text) => setCommonSyntax(text));
    fetch("SignatureSyntax.md")
      .then((res) => res.text())
      .then((text) => setSigSyntax(text));
    fetch("FormulaSyntax.md")
      .then((res) => res.text())
      .then((text) => setFormulaSyntax(text));
    fetch("TraceSyntax.md")
      .then((res) => res.text())
      .then((text) => setTraceSyntax(text));
  }, []);

  return (
    <Card style={{backgroundColor: "#fdd835"}} sx={{ width: '100%', height: '100%' }}>
      <CardContent>
        <Typography align="center" variant="h5">Syntax</Typography>
        <Divider variant="fullWidth"/>
        <Box sx={{ width: '100%', height: '100%' }}>
          <Box sx={{ borderBottom: 1, borderColor: 'divider' }}>
            <Tabs value={value} onChange={handleChange} aria-label="basic tabs example">
              <Tab label="Common" {...propses(0)} />
              <Tab label="Signature" {...propses(1)} />
              <Tab label="Formula" {...propses(2)} />
              <Tab label="Trace" {...propses(3)} />
            </Tabs>
          </Box>
          <CustomTabPanel value={value} index={0}>
            <ReactMarkdown rehypePlugins={[rehypeRaw]} children={commonSyntax} />
          </CustomTabPanel>
          <CustomTabPanel value={value} index={1}>
            <ReactMarkdown rehypePlugins={[rehypeRaw]} children={sigSyntax} />
          </CustomTabPanel>
          <CustomTabPanel value={value} index={2}>
            <ReactMarkdown rehypePlugins={[rehypeRaw]} children={formulaSyntax} />
          </CustomTabPanel>
          <CustomTabPanel value={value} index={3}>
            <ReactMarkdown rehypePlugins={[rehypeRaw]} children={traceSyntax} />
          </CustomTabPanel>
        </Box>
        <Box textAlign='center'>
          <Button variant='contained'
                  startIcon={<CloseIcon />}
                  onClick={() => setIsHelpCardVisible(false)}>
            Close
          </Button>
        </Box>
      </CardContent>
    </Card>
  );
}
