import React, { useState, useEffect, useRef, createRef } from 'react';
import ReactDOM from "react-dom";
import Box from '@mui/material/Box';
import Typography from '@mui/material/Typography';
import AceEditor from "react-ace";
import "ace-builds/src-noconflict/mode-java";
import "ace-builds/src-noconflict/theme-tomorrow";
import "ace-builds/src-noconflict/ext-language_tools";
import Keyboard from "react-simple-keyboard";
import "react-simple-keyboard/build/css/index.css";
import "../keyboard.css";

export default function FormulaTextField ({ formula, setFormState, fixParameters }) {

  const [localFormula, setLocalFormula] = useState("");

  const traceEditorHeight = window.innerHeight - 245;
  const editorHeight = fixParameters ? (window.innerHeight - 704).toString() + "px"
        : ((traceEditorHeight / 2) - 30).toString() + "px";

  const keyboard = useRef();

  const handleKeyboardChange = input => {
    setFormState({ type: 'setFormula', formula: input });
  };

  const handleChange = (event) => {
    const input = event;
    setFormState({ type: 'setFormula', formula: input });
    keyboard.current.setInput(input);
  };

  const initEditor = () => {
    return (
      <AceEditor
        mode="java"
        theme="tomorrow"
        name="formula"
        onChange={handleChange}
        width="100%"
        height={editorHeight}
        fontSize={14}
        showPrintMargin={false}
        showGutter={false}
        highlightActiveLine={false}
        value={formula}
        readOnly={fixParameters}
        setOptions={{
          enableBasicAutocompletion: false,
          enableLiveAutocompletion: false,
          enableSnippets: false,
          showLineNumbers: false,
          tabSize: 2,
        }}/>
    );
  };

  useEffect(() => {
    keyboard.current.setInput(formula);
  }, [formula]);

  return (
    <div>
      { !fixParameters && <Typography variant="h6" position="left">Formula</Typography> }
      <Box sx={{ width: '100%', height: '100%' }}
           className="editorBox">
        <div className="editor">
          { initEditor() }
        </div>
      </Box>
      <div className={`keyboardContainer ${fixParameters ? "hidden" : ""}`}>
        <Keyboard
          keyboardRef={r => (keyboard.current = r) }
          layoutName={"default"}
          onChange={handleKeyboardChange}
          layout={{
            default: ["∞ ⊤ ⊥ = ¬ ∧ ∨ → ↔ ∃ ∀ ● ○ ⧫ ◊ ■ □ S U"]
          }}
        />
      </div>
    </div>
  );
}
