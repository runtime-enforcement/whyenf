import * as React from 'react';
import Button from '@mui/material/Button';
import Dialog from '@mui/material/Dialog';
import DialogActions from '@mui/material/DialogActions';
import DialogContent from '@mui/material/DialogContent';
import DialogContentText from '@mui/material/DialogContentText';
import DialogTitle from '@mui/material/DialogTitle';

export default function ErrorDialog({ errorDialog, setErrorDialog }) {

  return (
    <Dialog
      open={errorDialog.open}
      onClose={() => setErrorDialog({ open: false, error: "" })}
      aria-labelledby="alert-dialog-title"
      aria-describedby="alert-dialog-description"
    >
      <DialogTitle id="alert-dialog-title">
        {"Error"}
      </DialogTitle>
      <DialogContent>
        <DialogContentText id="alert-dialog-description">
          {errorDialog.error}
        </DialogContentText>
      </DialogContent>
      <DialogActions>
        <Button onClick={() => setErrorDialog({ open: false, error: "" })} autoFocus>Close</Button>
      </DialogActions>
    </Dialog>
  );
}
