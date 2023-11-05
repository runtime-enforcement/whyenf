import React, { useState, useEffect } from 'react';
import Box from '@mui/material/Box';
import TextField from '@mui/material/TextField';
import Typography from '@mui/material/Typography';
import AceEditor from "react-ace";
import "ace-builds/src-noconflict/mode-java";
import "ace-builds/src-noconflict/theme-tomorrow";
import "ace-builds/src-noconflict/ext-language_tools";

const code = `export default uniquePropHOC(["time", "seconds"])(Expire);`;

export default function TraceTextField ({ trace, setFormState }) {

  const [localTrace, setLocalTrace] = useState("");
  const lines = 28;

  const handleChange = (event) => {
    // console.log(event.target.value);
    // setLocalTrace(event.target.value);
  };

  const handleBlur = (event) => {
    setFormState({ type: 'setTrace', trace: localTrace });
  };

  useEffect(() => {
    setLocalTrace(trace);
  }, [trace, setLocalTrace]);

  // return (
  // <Box
  //   component="form"
  //   sx={{
  //     '& .MuiTextField-root': { width: '100%' },
  //   }}
  //   noValidate
  //   autoComplete="off"
  // >
  //   <TextField
  //     id="outlined-multiline-static"
  //     label="Trace"
  //     required
  //     multiline
  //     value={localTrace}
  //     onChange={handleChange}
  //     onBlur={handleBlur}
  //     minRows={lines}
  //     maxRows={lines}
  //     InputProps={{ style: { fontSize: 14 } }}
  //   />
  // </Box>
  // );
  return (
    <div>
      <Typography variant="h6" position="left">Trace</Typography>
      <Box sx={{ width: '100%', height: '100%' }}
           className="editorBox">
        <div className="editor">
          <AceEditor
            placeholder=""
            mode="java"
            theme="tomorrow"
            name="trace"
    /* onLoad={this.onLoad} */
            onChange={handleChange}
            value={localTrace}
            width="100%"
            height="550px"
            fontSize={14}
            showPrintMargin={false}
            showGutter={false}
            highlightActiveLine={false}
            value={``}
            setOptions={{
              enableBasicAutocompletion: false,
              enableLiveAutocompletion: false,
              enableSnippets: false,
              showLineNumbers: false,
              tabSize: 2,
            }}/>
        </div>
      </Box>
    </div>
  );
}
