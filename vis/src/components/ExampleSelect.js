import React, { useState, useEffect } from 'react';
import Box from '@mui/material/Box';
import FormControl from '@mui/material/FormControl';
import Select from '@mui/material/Select';
import MenuItem from '@mui/material/MenuItem';
import InputLabel from '@mui/material/InputLabel';

const examples = [{
  name: 'publish-approve',
  formula: "publish(r) IMPLIES ONCE[0,604800] approve(r)",
  sig: "publish(x:int) approve(x:int)",
  trace: "@1307532861 approve (152) @1307955600 approve (163) publish (160) @1308477599 approve (187) publish (163) (152)"
}, {
  name: 'publish-approve-manager',
  formula: "publish(a,f) IMPLIES (ONCE[0,604800] (EXISTS m. (NOT mgr_F(m,a) SINCE mgr_S(m,a)) AND approve(m,f)))",
  sig: "publish (a:string, f:int) approve (m:string, f:int) mgr_S (m:string, a:string) mgr_F (m:string, a:string)",
  trace: "@1307532861 mgr_S (Mallory,Alice) mgr_S (Merlin,Bob) mgr_S (Merlin,Charlie) @1307532861 approve (Mallory,152) @1307955600 approve (Merlin,163) publish (Alice,160) mgr_F (Merlin,Charlie) @1308477599 approve (Merlin,187) publish (Bob,163) (Alice,163) (Charlie,163) (Charlie,152)"
}];

export default function ExampleSelect ({ setFormState }) {

  const [example, setExample] = useState("");

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
            <MenuItem value={"publish-approve"}>publish-approve</MenuItem>
            <MenuItem value={"publish-approve-manager"}>publish-approve-manager</MenuItem>
          </Select>
        </FormControl>
      </div>
    </Box>
  );
}
