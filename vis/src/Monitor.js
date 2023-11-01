import React, { useState, useReducer, useRef } from "react";
import Grid from '@mui/material/Grid';
import Box from '@mui/material/Box';
import Container from '@mui/material/Container';
import Draggable from 'react-draggable';
import TraceTextField from './components/TraceTextField';
import SigTextField from './components/SigTextField';
import AppendTraceTextField from './components/AppendTraceTextField';
import FormulaTextField from './components/FormulaTextField';
import TimeGrid from './components/TimeGrid';
import MonitorButton from './components/MonitorButton';
import HelpButton from './components/HelpButton';
import AppendButton from './components/AppendButton';
import LeaveButton from './components/LeaveButton';
import ResetButton from './components/ResetButton';
import ExampleSelect from './components/ExampleSelect';
import PreambleCard from './components/PreambleCard';
import AlertDialog from './components/AlertDialog';
import CheckmarkOptions from './components/CheckmarkOptions';
import SyntaxCheckBar from './components/SyntaxCheckBar';
import HelpCard from './components/HelpCard';
import { computeDbsTable, initRhsTable, initHovers, translateError } from './util';

function initMonitorState () {
  return { columns: { preds: [], subfs: [], subfsScopes: [] },
           objs: { dbs: [], expls: [] },
           tables: { dbs: [], colors: [], cells: [], hovers: [] },
           highlights: { selectedRows: [], highlightedCells: [], pathsMap: new Map() },
           subformulas: [],
           fixParameters: false,
           dialog: {},
           options: new Set()
         }
}

function initMonitor(monitorState, action) {
  try {
    const monitorOutput = window.monitorInit(action.trace.replace(/\n/g, " "),
                                             action.sig.replace(/\n/g, " "), action.formula);
    const columns = JSON.parse(window.getColumns(action.formula));
    const dbsObjs = (JSON.parse(monitorOutput)).dbs_objs
    const explsObjs = (JSON.parse(monitorOutput, (k, v) => v === "true" ? true : v === "false" ? false : v)).expls_objs;

    return { columns: { preds: columns.predsColumns, subfs: columns.subfsColumns, subfsScopes: columns.subfsScopes },
             objs: { dbs: dbsObjs, expls: explsObjs },
             tables: { dbs: computeDbsTable(dbsObjs, columns.predsColumns.length),
                       colors: initRhsTable(dbsObjs, columns.subfsColumns),
                       cells: initRhsTable(dbsObjs, columns.subfsColumns),
                       hovers: initHovers(dbsObjs, columns.subfsColumns) },
             highlights: { selectedRows: [],
                           highlightedCells: [],
                           pathsMap: new Map(),
                           subfsHeader: [] },
             subformulas: columns.subformulas,
             fixParameters: true,
             dialog: {},
             options: new Set() };
  } catch (error) {
    console.log(error);
    return { ...monitorState,
             dialog: translateError(error) };
  }
}

function execMonitor(monitorState, action) {
  try {

    const monitorOutput = window.monitorAppend(action.appendTrace.replace(/\n/g, " "), action.formula);
    const columns = JSON.parse(window.getColumns(action.formula));
    const dbsObjs = monitorState.objs.dbs.concat((JSON.parse(monitorOutput)).dbs_objs);
    const explsObjs = (JSON.parse(monitorOutput, (k, v) => v === "true" ? true : v === "false" ? false : v)).expls_objs;

    return { ...monitorState,
             objs: { dbs: dbsObjs, expls: monitorState.objs.expls.concat(explsObjs) },
             tables: { dbs: computeDbsTable(dbsObjs, columns.predsColumns.length),
                       colors: initRhsTable(dbsObjs, columns.subfsColumns),
                       cells: initRhsTable(dbsObjs, columns.subfsColumns),
                       hovers: initHovers(dbsObjs, columns.subfsColumns) },
             highlights: { selectedRows: [],
                           highlightedCells: [],
                           pathsMap: new Map(),
                           subfsHeader: [] },
             fixParameters: true,
             dialog: {} };

  } catch (error) {
    console.log(error);
    return { ...monitorState,
             dialog: translateError(error) };
  }
}

function formStateReducer(formState, action) {

  let newCheckedInputs;

  switch (action.type) {
  case 'setSig':
    newCheckedInputs = { ...formState.checkedInputs,
                         0: window.checkSignature(action.sig),
                         1: formState.checkedInputs[1] ? window.checkSignature(action.sig) : false
                       };
    return { ...formState,
             sig: action.sig,
             checkedInputs: newCheckedInputs
           };
  case 'setFormula':
    newCheckedInputs = { ...formState.checkedInputs,
                         1: formState.checkedInputs[0] ? window.checkFormula(action.formula) : false };
    return { ...formState,
             formula: action.formula,
             checkedInputs: newCheckedInputs
           };
  case 'setTrace':
    newCheckedInputs = { ...formState.checkedInputs,
                         2: window.checkLog(action.trace) };
    return { ...formState,
             trace: action.trace,
             checkedInputs: newCheckedInputs
           };
  case 'setFormulaAndTraceAndSig':
    newCheckedInputs = { 0: window.checkSignature(action.sig),
                         1: window.checkFormula(action.formula),
                         2: window.checkLog(action.trace)
                       };
    return { formula: action.formula,
             trace: action.trace,
             sig: action.sig,
             checkedInputs: newCheckedInputs
           };
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
  case 'updateColorsAndCellsTableAndColumns':
    return { ...monitorState,
             columns: {...monitorState.columns, subfs: action.subfsColumns },
             tables: { ...monitorState.tables,
                       colors: action.colorsTable,
                       cells: action.cellsTable,
                       hovers: action.hoversTable },
             highlights: { selectedRows: [],
                           highlightedCells: [],
                           pathsMap: new Map(),
                           subfsHeader: [] },
             fixParameters: true };
  case 'updateColorsAndCellsTable':
    return { ...monitorState,
             tables: { ...monitorState.tables,
                       colors: action.colorsTable,
                       cells: action.cellsTable,
                       hovers: action.hoversTable },
             highlights: { selectedRows: [],
                           highlightedCells: [],
                           pathsMap: new Map(),
                           subfsHeader: [] },
             fixParameters: true };
  case 'updateColorsAndCellsTableAndHighlights':
    return { ...monitorState,
             tables: { ...monitorState.tables,
                       colors: action.colorsTable,
                       cells: action.cellsTable,
                       hovers: action.hoversTable },
             highlights: { selectedRows: action.selectedRows,
                           highlightedCells: action.highlightedCells,
                           pathsMap: action.pathsMap,
                           subfsHeader: action.subfsHeader },
             fixParameters: true }
  case 'updateTable':
    return { ...monitorState,
             tables: { ...monitorState.tables,
                       colors: action.colorsTable },
             highlights: { selectedRows: action.selectedRows,
                           highlightedCells: action.highlightedCells,
                           pathsMap: action.pathsMap,
                           subfsHeader: action.subfsHeader },
             fixParameters: true };
  case 'resetTable':
    return { ...monitorState,
             tables: { ...monitorState.tables,
                       colors: initRhsTable(monitorState.objs.dbs,
                                            monitorState.columns.subfs,
                                            monitorState.columns.subfsScopes),
                       cells: initRhsTable(monitorState.objs.dbs,
                                           monitorState.columns.subfs,
                                           monitorState.columns.subfsScopes),
                       hovers: initRhsTable(monitorState.objs.dbs,
                                            monitorState.columns.subfs,
                                            monitorState.columns.subfsScopes)},
             highlights: { selectedRows: [],
                           highlightedCells: [],
                           pathsMap: new Map(),
                           subfsHeader: [] },
             fixParameters: true };
  case 'leaveMonitor':
    return initMonitorState ();
  case 'openDialog':
    return { ...monitorState,
             dialog: { name: action.name, message: action.message } };
  case 'closeDialog':
    return { ...monitorState,
             dialog: {} };
  case 'updateOptions':
    return { ...monitorState,
             options: new Set(action.options) };
  default:
    return monitorState;
  }
}

export default function Monitor() {

  const [appendTrace, setAppendTrace] = useState("");
  const [formState, setFormState] = useReducer(formStateReducer, { formula: "", trace: "", sig: "",
                                                                   checkedInputs: {0: false, 1: false, 2: false} });
  const [monitorState, setMonitorState] = useReducer(monitorStateReducer, initMonitorState ());
  const [isHelpCardVisible, setIsHelpCardVisible] = useState(false);
  const nodeRef = useRef(null);


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
    if (appendTrace === "") {
      action = { type: 'openDialog',
                 name: 'Error',
                 message: 'The trace provided is empty. Please try again.'
               };
    } else {
      action = { formula: formState.formula,
                 appendTrace: appendTrace,
                 type: 'appendTable'
               };
    }
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
    <Box style={{ height: '80vh', margin: 0, padding: 0 }}>

      { (monitorState.dialog !== undefined && (Object.keys(monitorState.dialog).length !== 0)) &&
        <AlertDialog open={true} dialog={monitorState.dialog} setMonitorState={setMonitorState} />
      }

      { isHelpCardVisible &&
        <Draggable nodeRef={nodeRef}
                   positionOffset={{ x: '100%', y: '15%' }}>
          <div className="draggable" ref={nodeRef}>
            <HelpCard setIsHelpCardVisible={setIsHelpCardVisible}/>
          </div>
        </Draggable>
      }

      <Container maxWidth={false}>
        <Box sx={{ mb: 12, mt: 12 }}>
          <Grid container spacing={3}>

            { !monitorState.fixParameters &&
              <Grid container item spacing={3}>
                <Grid container item spacing={2} xs={12} sm={12} md={6} lg={6} xl={6}>
                  <Grid item xs={12} sm={12} md={6} lg={6} xl={6}>
                    <ExampleSelect setFormState={setFormState} />
                  </Grid>
                  <Grid item xs={12} sm={12} md={4} lg={4} xl={4}>
                    <MonitorButton handleMonitor={handleMonitor} />
                  </Grid>
                  <Grid item xs={12} sm={12} md={2} lg={2} xl={2}>
                    <HelpButton isHelpCardVisible={isHelpCardVisible}
                                setIsHelpCardVisible={setIsHelpCardVisible} />
                  </Grid>
                </Grid>
                <Grid item xs={12} sm={12} md={6} lg={6} xl={6}>
                  <SyntaxCheckBar checkedInputs={formState.checkedInputs} />
                </Grid>
              </Grid>
            }

            { !monitorState.fixParameters &&
              <Grid container item xs={24} sm={24} md={12} lg={12} xl={12} spacing={3}>
                <Grid container item xs={12} sm={12} md={6} lg={6} xl={6} spacing={3}>
                  <Grid item xs={12} sm={12} md={12} lg={12} xl={12}>
                    <SigTextField sig={formState.sig} setFormState={setFormState} />
                  </Grid>
                  <Grid item xs={12} sm={12} md={12} lg={12} xl={12}>
                    <FormulaTextField formula={formState.formula}
                                      setFormState={setFormState}
                                      fixParameters={monitorState.fixParameters}/>
                  </Grid>
                </Grid>
                <Grid item xs={12} sm={12} md={6} lg={6} xl={6}>
                  <TraceTextField trace={formState.trace} setFormState={setFormState} />
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

            { monitorState.fixParameters &&
              <Grid container item xs={12} sm={12} md={8} lg={8} xl={8} spacing={2}>
                <Grid item xs={12} sm={12} md={8} lg={8} xl={8}>
                  <FormulaTextField formula={formState.formula}
                                    setFormState={setFormState}
                                    fixParameters={monitorState.fixParameters}
                  />
                </Grid>
                <Grid item xs={12} sm={12} md={4} lg={4} xl={4}>
                  <CheckmarkOptions selectedOptions={monitorState.options}
                                    setMonitorState={setMonitorState} />
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
                            selectedOptions={monitorState.options}
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
