import React, { useState, useEffect, createRef } from 'react';
import Box from '@mui/material/Box';
import AceEditor from "react-ace";
import "ace-builds/src-noconflict/mode-java";
import "ace-builds/src-noconflict/theme-tomorrow";
import "ace-builds/src-noconflict/ext-language_tools";

export default function AppendTraceTextField ({ appendTrace, setFormState }) {
  const [localTrace, setLocalTrace] = useState("");

  const editorHeight = (window.innerHeight - 704).toString() + "px";

  const handleChange = (event) => {
    setFormState({ type: 'setAppendTrace', appendTrace: event });
  };

  const initEditor = () => {
    return (
      <AceEditor
        mode="java"
        theme="tomorrow"
        name="sig"
        placeholder="New events"
        onChange={handleChange}
        width="100%"
        height={editorHeight}
        fontSize={14}
        showPrintMargin={false}
        showGutter={false}
        highlightActiveLine={false}
        value={appendTrace}
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
      <Box sx={{ width: '100%', height: '100%' }}
           className="editorBox">
        <div className="editor">
          { initEditor() }
        </div>
      </Box>
    </div>
  );
}
