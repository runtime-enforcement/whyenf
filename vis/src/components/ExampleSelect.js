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
}, {
  name: 'closed-publish-approve-manager',
  formula: "∀a. ∀f. publish(a,f) → (⧫[0,604800] (∃ m. (¬ mgr_F(m,a) S mgr_S(m,a)) ∧ approve(m,f)))",
  sig: "publish (a:string, f:int)\napprove (m:string, f:int)\nmgr_S (m:string, a:string)\nmgr_F (m:string, a:string)",
  trace: "@1307532861 mgr_S (Mallory, Alice) mgr_S (Merlin, Bob) mgr_S (Merlin, Charlie)\n@1307532861 approve (Mallory, 152)\n@1307955600 approve (Merlin, 163) publish (Alice, 160) mgr_F (Merlin, Charlie)\n@1308477599 approve (Merlin, 187) publish (Bob, 163) (Alice, 163) (Charlie, 163) (Charlie, 152)\n"
}, {
  name: 'data-race',
  formula: "((ONCE (read(t1,x) OR write(t1,x))) AND (ONCE write(t2,x))) IMPLIES EXISTS l. ((NOT ONCE NOT ((read(t1,x) OR write(t1,x)) IMPLIES (NOT rel(t1,l) SINCE acq(t1,l)))) AND (NOT ONCE NOT ((read(t2,x) OR write(t2,x)) IMPLIES (NOT rel(t2,l) SINCE acq(t2,l)))))",
  sig: "acq(x:int,y:int)\nrel(x:int,y:int)\nread(x:int,y:int)\nwrite(x:int,y:int)\n",
  trace: "@0 acq(9,9)\n@1 read(9,3)\n@2 acq(13,19)\n@3 acq(15,3)\n@4 acq(18,15)\n@5 read(13,5)\n@6 write(15,4)\n@7 write(15,3)\n@8 acq(17,13)\n@9 write(15,9)\n@10 write(13,13)\n@11 acq(8,11)\n@12 write(18,4)\n@13 rel(9,9)\n@14 acq(10,10)\n@15 read(15,4)\n@16 write(15,9)\n@17 write(13,10)\n@18 acq(7,6)\n@19 acq(0,5)\n"
}, {
  name: 'enf-open-close',
  formula: "(∃x. open(x) ∧ ⧫[0,5] close(x)) ∨ (∃y. ¬close(y) ∧ (¬close(y) S[5,∞) open(y)))",
  sig: "open (x:int)\nclose (y:int)\n",
  trace: "@0 open(1)\n@1 close(2)\n@5 open(2)\n"
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
            <MenuItem value={"closed-publish-approve-manager"}>closed-publish-approve-manager</MenuItem>
            <MenuItem value={"data-race"}>data-race</MenuItem>
            <MenuItem value={"enf-open-close"}>enf-open-close</MenuItem>
          </Select>
        </FormControl>
      </div>
    </Box>
  );
}
