import React, { useState, useEffect } from 'react';
import Box from '@mui/material/Box';
import FormControl from '@mui/material/FormControl';
import Select from '@mui/material/Select';
import MenuItem from '@mui/material/MenuItem';
import InputLabel from '@mui/material/InputLabel';

const examples = [{
  name: 'publish-approve',
  formula: "publish(r) → ⧫[0,604800] approve(r)",
  sig: "publish(x:int)\napprove(x:int)",
  trace: "@1307532861 approve (152)\n@1307955600 approve (163) publish (160)\n@1308477599 approve (187) publish (163) (152)\n"
}, {
  name: 'publish-approve-manager',
  formula: "publish(a,f) → (⧫[0,604800] (∃ m. (¬ mgr_F(m,a) S mgr_S(m,a)) ∧ approve(m,f)))",
  sig: "publish (a:string, f:int)\napprove (m:string, f:int)\nmgr_S (m:string, a:string)\nmgr_F (m:string, a:string)",
  trace: "@1307532861 mgr_S (Mallory, Alice) mgr_S (Merlin, Bob) mgr_S (Merlin, Charlie)\n@1307532861 approve (Mallory, 152)\n@1307955600 approve (Merlin, 163) publish (Alice, 160) mgr_F (Merlin, Charlie)\n@1308477599 approve (Merlin, 187) publish (Bob, 163) (Alice, 163) (Charlie, 163) (Charlie, 152)\n"
}];

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
