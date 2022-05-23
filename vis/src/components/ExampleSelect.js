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
  }, {
    name: 'recurbqr-past',
    formula: "(r AND (NOT q) AND (ONCE q)) => ((ONCE[0,3] (p OR q)) SINCE q)",
    trace: "@0 q\n@1 p\n@2 r\n@3 q\n@4 \n@5 \n@6 p\n@7 \n@8 p\n@9 \n@10 \n@11 p\n@12 p\n@13 \n@14 p\n@15 p\n@16 r\n@17 q\n@18 p\n@19 \n@20 p\n@21 \n@22 \n@23 p\n@24 p\n@25 p\n@26 \n@27 p\n@28 \n@29 r\n@30 \n@31 q\n@32 \n@33 \n@34 p\n@35 p\n@36 p\n@37 \n@38 \n@39 p\n@40 p\n@41 r\n@42 q\n@43 \n@44 p\n@45 \n@46 \n@47 p\n@48 \n@49 \n@50 p\n@51 \n@52 \n@53 r\n@54 \n@55 \n@56 q\n@57 \n@58 \n@59 \n@60 \n@61 r"
  }, {
    name: 'since-conjunction',
    formula: "a SINCE[1,2] (b AND c)",
    trace: "@1 a b c\n@3 a b\n@3 a b \n@3 \n@3 a\n@4 a"
  }, {
    name: 'respondbqr-past',
    formula: "(r AND (NOT q) AND (ONCE q)) => (((s => (ONCE[0,3] p)) AND (NOT((NOT s) SINCE[3, INFINITY] p))) SINCE q)",
    trace: "@0 q\n@1 \n@2 p\n@3 \n@4 s\n@5 \n@6 p\n@7 s\n@8 \n@9 p\n@10 \n@11 \n@12 s\n@13 \n@14 p\n@15 \n@16 \n@17 s\n@18 \n@19 p\n@20 \n@21 \n@22 s\n@23 \n@24 p\n@25 s\n@26 \n@27 p\n@28 s\n@29 \n@30 r\n@31 q\n@32 \n@33 p\n@34 \n@35 \n@36 s\n@37 \n@38 p\n@39 s\n@40 \n@41 p\n@42 \n@43 s\n@44 \n@45 p\n@46 \n@47 \n@48 s\n@49 \n@50 p\n@51 s\n@52 \n@53 p\n@54 \n@55 s\n@56 \n@57 r\n@58 q\n@59 p\n@60 \n@61 \n@62 \n@63 \n@64 r"
  }];

  const handleChange = (event) => {
    setExample(event.target.value);
  };

  const handleClose = (event) => {
    const result = examples.find( ({ name }) => name === example );
    if (result !== undefined) {
      setFormState({ type: 'setFormulaAndTrace', formula: result.formula, trace: result.trace });
    }
  };

  useEffect(() => {
    const result = examples.find( ({ name }) => name === example );
    if (result !== undefined) {
      setFormState({ type: 'setFormulaAndTrace', formula: result.formula, trace: result.trace });
    }
  }, [example, setFormState, examples]);

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
            <MenuItem value={"since-conjunction"}>Since (conjunction)</MenuItem>
            <MenuItem value={"recurbqr-past"}>Bounded Recurrence</MenuItem>
            <MenuItem value={"respondbqr-past"}>Bounded Response</MenuItem>
          </Select>
        </FormControl>
      </div>
    </Box>
  );
}
