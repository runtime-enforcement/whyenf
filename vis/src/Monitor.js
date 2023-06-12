import React, { useState, useReducer } from "react";
import Grid from '@mui/material/Grid';
import Box from '@mui/material/Box';
import Container from '@mui/material/Container';
import TraceTextField from './components/TraceTextField';
import SigTextField from './components/SigTextField';
import AppendTraceTextField from './components/AppendTraceTextField';
import FormulaTextField from './components/FormulaTextField';
import TimeGrid from './components/TimeGrid';
import MonitorButton from './components/MonitorButton';
import AppendButton from './components/AppendButton';
import LeaveButton from './components/LeaveButton';
import ResetButton from './components/ResetButton';
import ExampleSelect from './components/ExampleSelect';
import PreambleCard from './components/PreambleCard';
import AlertDialog from './components/AlertDialog';
import { computeDbsTable, translateError } from './util';

function initMonitorState () {
  return { columns: { preds: [], subfs: [] },
           objs: { dbs: [], expls: [] },
           tables: { dbs: [], expls: [] },
           highlights: { selectedRows: [], highlightedCells: [], pathsMap: new Map() },
           subformulas: [],
           jsooMonitorState: [],
           fixParameters: false,
           dialog: {} }
}

function initMonitor(monitorState, action) {
  try {
    const monitor = window.monitorInit(action.trace.replace(/\n/g, " "),
                                       action.sig.replace(/\n/g, " "), action.formula);
    const columns = JSON.parse(window.getColumns(action.formula));
    const dbsObjs = (JSON.parse(monitor[2])).dbs_objs;
    const explsObjs = (JSON.parse(monitor[2])).expls_objs;
    const jsooMonitorState = monitor[1];
    dbsObjs.nCols = columns.predsColumns.length;

    return { columns: { preds: columns.predsColumns, subfs: columns.subfsColumns },
             objs: { dbs: dbsObjs, expls: explsObjs },
             tables: { dbs: computeDbsTable(dbsObjs), expls: [] },
             highlights: { selectedRows: [], highlightedCells: [], pathsMap: new Map() },
             subformulas: columns.subformulas,
             jsooMonitorState: jsooMonitorState,
             fixParameters: true,
             dialog: {} };
  } catch (error) {
    console.log(error);
    return { ...monitorState,
             dialog: translateError(error) };
  }
}

function execMonitor(monitorState, action) {
  try {

    const monitor = window.monitorAppend(action.trace.replace(/\n/g, " "),
                                         action.formula, action.jsooMonitorState);
    const columns = JSON.parse(window.getColumns(action.formula));
    const dbsObjs = (JSON.parse(monitor[2])).dbs_objs;
    const explsObjs = (JSON.parse(monitor[2])).expls_objs;
    const jsooMonitorState = monitor[1];
    dbsObjs.nCols = columns.predsColumns.length;

    return { ...monitorState,
             objs: { dbs: dbsObjs, expls: explsObjs },
             tables: { dbs: computeDbsTable(dbsObjs), expls: [] },
             highlights: { selectedRows: [], highlightedCells: [], pathsMap: new Map() },
             jsooMonitorState: jsooMonitorState,
             fixParameters: true,
             dialog: {} };
  } catch (error) {
    console.log(error);
    return { ...monitorState,
             dialog: translateError(error) };
  }
}

function formStateReducer(formState, action) {
  switch (action.type) {
  case 'setFormula':
    return { ...formState,
             formula: action.formula };
  case 'setTrace':
    return { ...formState,
             trace: action.trace };
  case 'setSig':
    return { ...formState,
             sig: action.sig };
  case 'setFormulaAndTraceAndSig':
    return { formula: action.formula,
             trace: action.trace,
             sig: action.sig };
  default:
    return formState;
  }
}

function monitorStateReducer(monitorState, action) {
  switch (action.type) {
  case 'initTable':
    return initMonitor(monitorState, action);
  case 'appendTable':
    return execMonitor(monitorState, action);
  case 'updateTable':
    return { ...monitorState,
             tables: { dbs: action.dbsTable, expls: action.explsTable },
             highlights: { selectedRows: action.selectedRows,
                           highlightedCells: action.highlightedCells,
                           pathsMap: action.pathsMap },
             fixParameters: true };
  case 'resetTable':
    return { ...monitorState,
             tables: { dbs: computeDbsTable(monitorState.objs.dbs) },
             highlights: { selectedRows: [],
                           highlightedCells: [],
                           pathsMap: new Map() },
             fixParameters: true };
  case 'leaveMonitor':
    return initMonitorState ();
  case 'openDialog':
    return { ...monitorState,
             dialog: { name: action.name, message: action.message } };
  case 'closeDialog':
    return { ...monitorState,
             dialog: {} };
  default:
    return monitorState;
  }
}

export default function Monitor() {

  const [appendTrace, setAppendTrace] = useState("");
  const [formState, setFormState] = useReducer(formStateReducer, { formula: "", trace: "", sig: "" });
  const [monitorState, setMonitorState] = useReducer(monitorStateReducer,
                                                     initMonitorState ());

  const handleMonitor = (e) => {
    e.preventDefault();

    let action = { formula: formState.formula,
                   trace: formState.trace,
                   sig: formState.sig,
                   type: 'initTable'
                 };

    setMonitorState(action);
  };

  const handleAppend = (e) => {
    e.preventDefault();

    let action;
    if (appendTrace === "") action = { type: 'openDialog',
                                       name: 'Error',
                                       message: 'Your trace is empty. Please try again.'
                                     };
    else action = { formula: formState.formula,
                    appendTrace: appendTrace,
                    jsooMonitorState: monitorState.jsooMonitorState,
                    type: 'appendTable'
                  };

    setMonitorState(action);
  };

  const handleReset = (e) => {
    e.preventDefault();
    let action = { type: 'resetTable' };
    setMonitorState(action);
  }

  const handleLeave = (e) => {
    e.preventDefault();
    let action = { type: 'leaveMonitor' };
    setMonitorState(action);
  };

  return (
    <Box style={{ height: '100vh', margin: 0, padding: 0 }}>
      { (monitorState.dialog !== undefined && (Object.keys(monitorState.dialog).length !== 0)) &&
        <AlertDialog open={true} dialog={monitorState.dialog} setMonitorState={setMonitorState} />
      }
      <Container maxWidth={false}>
        <Box sx={{ mb: 12 }}>
          <Grid container spacing={2}>
            <Grid item xs={12} sm={12} md={12} lg={12} xl={12}>
              <PreambleCard />
            </Grid>
            { !monitorState.fixParameters &&
              <Grid container item xs={12} sm={12} md={4} lg={4} xl={4} spacing={2}>
                <Grid item xs={12} sm={12} md={6} lg={6} xl={6}>
                  <ExampleSelect setFormState={setFormState} />
                </Grid>
                <Grid item xs={12} sm={12} md={6} lg={6} xl={6}>
                  <MonitorButton handleMonitor={handleMonitor} />
                </Grid>
              </Grid>
            }

            { monitorState.fixParameters &&
              <Grid container item xs={12} sm={12} md={4} lg={4} xl={4} spacing={2}>
                <Grid item xs={12} sm={12} md={6} lg={6} xl={6}>
                  <AppendTraceTextField appendTrace={appendTrace} setAppendTrace={setAppendTrace} />
                </Grid>
                <Grid item xs={12} sm={12} md={2} lg={2} xl={2}>
                  <AppendButton handleAppend={handleAppend} />
                </Grid>
                <Grid item xs={12} sm={12} md={2} lg={2} xl={2}>
                  <ResetButton handleReset={handleReset} />
                </Grid>
                <Grid item xs={12} sm={12} md={2} lg={2} xl={2}>
                  <LeaveButton handleLeave={handleLeave} />
                </Grid>
              </Grid>
            }

            <Grid item xs={12} sm={12} md={8} lg={8} xl={8}>
              <FormulaTextField formula={formState.formula}
                                setFormState={setFormState}
                                fixParameters={monitorState.fixParameters}
              />
            </Grid>

            { !monitorState.fixParameters &&
              <Grid container item xs={24} sm={24} md={12} lg={12} xl={12} spacing={2}>
                <Grid container item xs={12} sm={12} md={4} lg={4} xl={4} spacing={2}>
                  <Grid item xs={12} sm={12} md={12} lg={12} xl={12}>
                    <TraceTextField trace={formState.trace} setFormState={setFormState} />
                  </Grid>
                  <Grid item xs={12} sm={12} md={12} lg={12} xl={12}>
                    <SigTextField sig={formState.sig} setFormState={setFormState} />
                  </Grid>
                </Grid>
                <Grid item xs={12} sm={12} md={8} lg={8} xl={8}>
                  <TimeGrid columns={monitorState.columns}
                            objs={monitorState.objs}
                            tables={monitorState.tables}
                            subformulas={monitorState.subformulas}
                            setMonitorState={setMonitorState}
                  />
                </Grid>
              </Grid>
            }


            { monitorState.fixParameters &&
              <Grid container item xs={24} sm={24} md={12} lg={12} xl={12} spacing={2}>
                <Grid item xs={24} sm={24} md={12} lg={12} xl={12}>
                  <TimeGrid columns={monitorState.columns}
                            objs={monitorState.objs}
                            tables={monitorState.tables}
                            highlights={monitorState.highlights}
                            subformulas={monitorState.subformulas}
                            setMonitorState={setMonitorState}
                  />
                </Grid>
              </Grid>
            }
          </Grid>
        </Box>
      </Container>
    </Box>
  );
}
