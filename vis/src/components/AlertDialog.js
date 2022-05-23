import * as React from 'react';
import Button from '@mui/material/Button';
import Dialog from '@mui/material/Dialog';
import DialogActions from '@mui/material/DialogActions';
import DialogContent from '@mui/material/DialogContent';
import DialogContentText from '@mui/material/DialogContentText';
import DialogTitle from '@mui/material/DialogTitle';
import ErrorIcon from '@mui/icons-material/Error';

export default function AlertDialog({ open, dialog, setMonitorState }) {

  return (
    <Dialog
      open={open}
      onClose={() => setMonitorState({ type: "closeDialog" })}
      aria-labelledby="alert-dialog-title"
      aria-describedby="alert-dialog-description"
    >
      <DialogTitle id="alert-dialog-title">
        {dialog.name === "Error" && <ErrorIcon sx={{ fontSize: 30, mb: -1, pr: 1 }} /> }
        {dialog.name}
      </DialogTitle>
      <DialogContent>
        <DialogContentText id="alert-dialog-description" sx={{ whiteSpace: 'break-spaces' }}>
          {dialog.message}
        </DialogContentText>
      </DialogContent>
      <DialogActions>
        <Button onClick={() => setMonitorState({ type: "closeDialog" })} autoFocus>Close</Button>
      </DialogActions>
    </Dialog>
  );
}
