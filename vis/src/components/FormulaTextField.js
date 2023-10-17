import React, { useState, useEffect, useRef } from 'react';
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
  const [isKeyboardOpen, setKeyboardOpen] = useState(false);
  const keyboard = useRef();

  const openKeyboard = () => {
    setKeyboardOpen(true);
  };

  const closeKeyboard = () => {
    setKeyboardOpen(false);
  };

  const onChange = input => {
    setLocalFormula(input);
  };

  const handleChange = (event) => {
    const input = event.target.value;
    setLocalFormula(input);
    keyboard.current.setInput(input);
  };

  const handleBlur = (event) => {
    setKeyboardOpen(false, setFormState({ type: 'setFormula', formula: localFormula }));
  };

  useEffect(() => {
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
    >
      <div>
        <TextField
          required
          id="outlined-required"
          label="Formula"
          value={localFormula}
          onChange={handleChange}
          onBlur={handleBlur}
          onFocus={openKeyboard}
          disabled={fixParameters}
        />
        <div className={`keyboardContainer ${!isKeyboardOpen ? "hidden" : ""}`}>
          <Keyboard
            keyboardRef={r => (keyboard.current = r)}
            layoutName={"default"}
            onChange={onChange}
            layout={{
              default: ["⊤ ⊥ = ¬ ∧ ∨ → ↔ ∃ ∀ ● ○ ⧫ ◊ ■ □"]
            }}
          />
        </div>
      </div>
    </Box>
  );
}
