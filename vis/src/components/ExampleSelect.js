import React, { useState, useEffect } from 'react';
import Box from '@mui/material/Box';
import FormControl from '@mui/material/FormControl';
import Select from '@mui/material/Select';
import MenuItem from '@mui/material/MenuItem';
import InputLabel from '@mui/material/InputLabel';
import localJSON from './examples';

const examples = localJSON.examples;

export default function ExampleSelect ({ setFormState }) {

  const [example, setExample] = useState("");

  const handleChange = (event) => {
    setExample(event.target.value);
  };

  const handleClose = (event) => {
    const result = examples.find( ({ name }) => name === example );
    if (result !== undefined) {
      setFormState({ type: 'setFormulaAndTraceAndSig', formula: result.formula, trace: result.trace, sig: result.sig });
    }
  };

  useEffect(() => {
    const result = examples.find( ({ name }) => name === example );
    if (result !== undefined) {
      setFormState({ type: 'setFormulaAndTraceAndSig', formula: result.formula, trace: result.trace, sig: result.sig });
    }
  }, [example, setFormState, examples]);

  return (
    <Box
      component="form"
      sx={{
        '& .MuiTextField-root': { width: '100%', height: '100%' },
      }}
      noValidate
      autoComplete="off"
    >
      <div>
        <FormControl fullWidth>
          <InputLabel id="example-select-label">Example</InputLabel>
          <Select
            id="example-select"
            label="Example"
            value={example}
            onChange={handleChange}
            onClose={handleClose}
          >
            {/* <MenuItem value={"publish-approve-unix-ts"}>publish-approve-unix-ts</MenuItem> */}
            <MenuItem value={"publish-approve-manager"}>Publish/Approve</MenuItem>
            {/* <MenuItem value={"publish-approve-manager-unix-ts"}>publish-approve-manager-unix-ts</MenuItem> */}
            <MenuItem value={"closed-publish-approve-manager"}>Closed Publish/Approve</MenuItem>
            <MenuItem value={"data-race"}>Data Race</MenuItem>
            <MenuItem value={"nokia-del-2-3"}>Database Deletion Propagation</MenuItem>
          </Select>
        </FormControl>
      </div>
    </Box>
  );
}
