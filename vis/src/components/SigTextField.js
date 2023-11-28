import React, { useState, useRef } from 'react';
import Box from '@mui/material/Box';
import Typography from '@mui/material/Typography';
import AceEditor from "react-ace";
import "ace-builds/src-noconflict/mode-mfotl_signature";
import "ace-builds/src-noconflict/theme-tomorrow";
import "ace-builds/src-noconflict/ext-language_tools";

export default function SigTextField ({ sig, setFormState }) {

  const [isFocused, setIsFocused] = useState(false);

  const traceEditorHeight = window.innerHeight - 245;
  const editorHeight = ((traceEditorHeight / 2) - 80).toString() + "px";

  const aceEditor = useRef();

  const handleChange = (event) => {
    setFormState({ type: 'setSig', sig: event });
  };

  const handleFocus = () => {
    setIsFocused(true);
  };

  const handleBlur = () => {
    setIsFocused(false);
  };

  const initEditor = () => {
    return (
      <AceEditor
        ref={aceEditor}
        mode="mfotl_signature"
        theme="tomorrow"
        name="sig"
        onChange={handleChange}
        onFocus={handleFocus}
        onBlur={handleBlur}
        width="100%"
        height={editorHeight}
        fontSize={14}
        showPrintMargin={false}
        showGutter={false}
        highlightActiveLine={false}
        value={sig}
        setOptions={{
          enableBasicAutocompletion: false,
          enableLiveAutocompletion: false,
          enableSnippets: false,
          showLineNumbers: false,
          tabSize: 2,
        }}/>
    );
  };

  return (
    <div>
      <Typography variant="h6" position="left">Signature</Typography>
      <Box sx={{ width: '100%', height: '100%' }}
           className={isFocused ? "focusedEditorBox" : "editorBox"}>
        <div className="editor">
          { initEditor() }
        </div>
      </Box>
    </div>
  );
}
