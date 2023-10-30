import React, { useState, useEffect, useRef, createRef } from 'react';
import ReactDOM from "react-dom";
import Box from '@mui/material/Box';
import TextField from '@mui/material/TextField';
import Grid from '@mui/material/Grid';
import Container from '@mui/material/Container';
import Keyboard from "react-simple-keyboard";
import "react-simple-keyboard/build/css/index.css";
import "../keyboard.css";

export default function FormulaTextField ({ formula, setFormState, fixParameters }) {

  const [localFormula, setLocalFormula] = useState("");
  const [rows, setRows] = useState(12);

  const keyboard = useRef();
  const ref = createRef();

  const handleKeyboardChange = input => {
    setLocalFormula(input, setFormState({ type: 'setFormula', formula: input }));
  };

  const handleChange = (event) => {
    const input = event.target.value;
    setLocalFormula(input);
    keyboard.current.setInput(input);
  };

  const handleBlur = (event) => {
    setFormState({ type: 'setFormula', formula: localFormula });
  };

  useEffect(() => {
    setRows(ref.current.clientHeight/27);
    keyboard.current.setInput(formula);
    setLocalFormula(formula);
  }, [formula, setLocalFormula]);

  return (
    <Box
      component="form"
      sx={{
        '& .MuiTextField-root': { width: '100%' },
      }}
      noValidate
      autoComplete="off"
      ref={ref}
    >
      <div>
        <TextField
          required
          multiline
          id="outlined-required"
          label="Formula"
          value={localFormula}
          onChange={handleChange}
          onBlur={handleBlur}
          disabled={fixParameters}
          minRows={rows}
          maxRows={rows}
          InputProps={{style: { minHeight: '35vh',
                                maxHeight: '35vh',
                                fontSize: 14
                              }
                      }}
        />
        <div className={`keyboardContainer ${fixParameters ? "hidden" : ""}`}>
          <Keyboard
            keyboardRef={r => (keyboard.current = r) }
            layoutName={"default"}
            onChange={handleKeyboardChange}
            layout={{
              default: ["⊤ ⊥ = ¬ ∧ ∨ → ↔ ∃ ∀ ● ○ ⧫ ◊ ■ □"]
            }}
          />
        </div>
      </div>
    </Box>
  );
}
