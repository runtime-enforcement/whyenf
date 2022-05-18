import React, { useState, useEffect } from 'react';
import Box from '@mui/material/Box';
import FormControl from '@mui/material/FormControl';
import Select from '@mui/material/Select';
import MenuItem from '@mui/material/MenuItem';
import InputLabel from '@mui/material/InputLabel';

export default function ExampleSelect ({ setFormState }) {

  const [example, setExample] = useState("");

  const examples = [{
    name: 'intrusion-detection',
    formula: "NOT((out1 AND (PREV (ONCE in1) AND (EVENTUALLY[0,60] ids1))) OR (out2 AND (PREV (ONCE in2) AND (EVENTUALLY[0,60] ids2))) OR (out3 AND (PREV (ONCE in3) AND (EVENTUALLY[0,60] ids3))))",
    trace: "@1 in1\n@2 in2 in3\n@50 out1\n@51 out2 out3\n@59 ids1\n@63 ids3"
  }];

  const handleChange = (event) => {
    setExample(event.target.value);
  };

  const handleClose = (event) => {
    const result = examples.find( ({ name }) => name === example );
    if (result !== undefined) {
      console.log("Hi!");
      console.log(result);
      setFormState({ type: 'setFormulaAndTrace', formula: result.formula, trace: result.trace });
    }
  };

  useEffect(() => {
    const result = examples.find( ({ name }) => name === example );
    if (result !== undefined) {
      setFormState({ type: 'setFormulaAndTrace', formula: result.formula, trace: result.trace });
    }
  }, [example, setFormState]);

  return (
    <Box
      component="form"
      sx={{
        '& .MuiTextField-root': { width: '100%' },
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
            <MenuItem value={"intrusion-detection"}>Intrusion Detection</MenuItem>
          </Select>
        </FormControl>
      </div>
    </Box>
  );
}
