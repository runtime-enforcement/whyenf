import React, { useState, useEffect } from 'react';
import Box from '@mui/material/Box';
import { DataGrid } from '@mui/x-data-grid';
import Button from '@mui/material/Button';
import CircleIcon from '@mui/icons-material/Circle';
import CancelIcon from '@mui/icons-material/Cancel';
import CheckCircleIcon from '@mui/icons-material/CheckCircle';
import StorageIcon from '@mui/icons-material/Storage';
import Popover from '@mui/material/Popover';
import { red, amber, lightGreen, blueGrey, teal } from '@mui/material/colors';
import { common } from '@mui/material/colors';
import { black, cellColor, updateHighlights, getHeaderHighlights, updateHovers } from '../util';
import MenuCell from './MenuCell';
import DbTable from './DbTable';
import HoverTable from './HoverTable';

function DbCell(props) {
  if (props.value.length === 0) {
    return (
      <Button>
        <CancelIcon style={{ color: red[500] }} />
      </Button>
    );
  } else {
    return (
      <Button>
        <StorageIcon style={{ color: black }} />
      </Button>
    );
  }
}

function BoolCell(props) {
  if (props.value === red[500] || props.value === lightGreen[500] || props.value === black) {
    return (
      <Button onClick={props.onClick}>
        { props.value === black && <CircleIcon style={{ color: props.value }} /> }
        { props.value === red[500] && <CancelIcon style={{ color: props.value }} /> }
        { props.value === lightGreen[500] && <CheckCircleIcon style={{ color: props.value }} /> }
      </Button>
    );
  } else {
    return "";
  }
}

function TimeGrid ({ columns,
                     objs,
                     tables,
                     highlights,
                     subformulas,
                     selectedOptions,
                     setMonitorState }) {

  const [anchorEl, setAnchorEl] = useState(null);
  const [anchorValue, setAnchorValue] = useState({});
  const open = Boolean(anchorEl);

  const handlePopoverOpen = (event) => {
    const row = event.currentTarget.parentElement.dataset.id;
    const col = parseInt(event.currentTarget.dataset.field);

    // Preds
    if (col < columns.preds.length &&
        tables.dbs[row][col].length !== 0) {
      setAnchorValue({ kind: "db", value: tables.dbs[row][col] });
      setAnchorEl(event.currentTarget);
    }

    // Subformulas
    if (col >= columns.preds.length &&
        tables.colors[row][col - columns.preds.length] !== "" &&
        tables.colors[row][col - columns.preds.length] !== black &&
        tables.cells[row][col - columns.preds.length].kind !== undefined &&
        tables.cells[row][col - columns.preds.length].kind !== "partition") {
      setAnchorValue({ kind: "subf",
                       table: tables.hovers[row][col - columns.preds.length],
                       subf: subformulas[col - columns.preds.length] });
      setAnchorEl(event.currentTarget);
    }
  };

  const handlePopoverClose = () => {
    setAnchorEl(null);
  };

  // Preds columns
  const predsWidth = columns.preds.reduce ((acc, pred) =>
    Math.max(acc, (8*(pred.length))), 50
  );

  const predsGridColumns = columns.preds.slice(0).map((p, i) =>
    ({
      field: i.toString(),
      headerName: p,
      width: predsWidth,
      sortable: false,
      renderHeader: () => p,
      // renderCell: (params) => <DbCell value={tables.dbs[params.row.tp][i]} />,
      renderCell: (params) => <DbCell value={tables.dbs[params.row.tp][i]} />,
      headerAlign: 'center',
      align: 'center',
      disableClickEventBubbling: true,
      hide: !selectedOptions.has('Trace')
    }));

  // TP/TS columns
  const tsWidth = objs.dbs.reduce ((acc, { ts, tp }) =>
    selectedOptions.has('Unix Timestamps') ?
      Math.max(acc, (9*((new Date(ts).toLocaleString()).length)))
      : Math.max(acc, (10*(ts.toString().length))), 50
  );

  const tptsGridColumns = [
    {
      field: 'tp',
      headerName: <b>TP</b>,
      width: 70,
      sortable: false,
      headerAlign: 'center',
      align: 'center',
      disableClickEventBubbling: true
    },
    { field: 'ts',
      headerName: <b>TS</b>,
      width: tsWidth,
      sortable: false,
      headerAlign: 'center',
      align: 'center',
      disableClickEventBubbling: true
    }
  ];

  // Values column
  const valuesGridColumn = [
    {
      field: 'values',
      headerName: <b>Values</b>,
      width: 80,
      sortable: false,
      headerAlign: 'center',
      align: 'center',
      disableClickEventBubbling: true,
      renderCell: (params) => {
        if (objs.expls[params.id] !== undefined) {
          return <MenuCell explObj={objs.expls[params.id].expl}
                           colorsTable={tables.colors}
                           cellsTable={tables.cells}
                           hoversTable={tables.hovers}
                           curCol={0}
                           setMonitorState={setMonitorState} />;
        } else {
          return "";
        }
      }
    }
  ];

  // Subfs columns
  const subfsWidth = columns.subfs.reduce((acc, subf) =>
    Math.max(acc, (8*(subf.length))), 60
  );

  // colGridIndex: index of the column in the grid
  // i/curCol: index of the column in the subformulas part of the grid (i.e., after the TS column)
  const subfsGridColumns = columns.subfs.slice(0).map((f, i) =>
    ({
      field: (i+columns.preds.length).toString(),
      headerName: f,
      headerClassName: () => {
        if (highlights.subfsHeader[i] === "curHighlight") {
          return "columnHeader--CurHighlighted";
        } else {
          if (highlights.subfsHeader[i] === "leftHighlight") {
            return "columnHeader--LeftHighlighted";
          } else {
            if (highlights.subfsHeader[i] === "rightHighlight") {
              return "columnHeader--RightHighlighted";
            } else {
              return "";
            }
          }
        }
      },
      width: subfsWidth,
      sortable: false,
      renderHeader: () => f,
      renderCell: (params) => {
        if (f.charAt(0) === '∃' || f.charAt(0) === '∀') {
          if (tables.cells[params.row.tp][i].kind === "partition" &&
              (tables.colors[params.row.tp][i] === red[500]
               || tables.colors[params.row.tp][i] === lightGreen[500])) {
            return <MenuCell explObj={tables.cells[params.row.tp][i]}
                             colorsTable={tables.colors}
                             cellsTable={tables.cells}
                             hoversTable={tables.hovers}
                             ts={params.row.ts}
                             tp={params.row.tp}
                             colGridIndex={parseInt(params.colDef.field)}
                             curCol={i}
                             predsLength={columns.preds.length}
                             dbsObjs={objs.dbs}
                             highlights={highlights}
                             setMonitorState={setMonitorState}
                             subfsScopes={columns.subfsScopes}/>;
          }
        }
        return <BoolCell value={tables.colors[params.row.tp][i]}
                         onClick={() => handleClick(params.row.ts, params.row.tp, parseInt(params.colDef.field))}
               />;
      },
      headerAlign: 'center',
      align: 'center',
      disableClickEventBubbling: true
    }));

  const rows = objs.dbs.map(({ ts, tp }) =>
    ({
      id: tp,
      tp: tp,
      ts: selectedOptions.has('Unix Timestamps') ? new Date(ts*1000).toLocaleString() : ts
    }));

  const handleClick = (ts, tp, colGridIndex) => {

    let cell = tables.cells[tp][colGridIndex - columns.preds.length];

    if (cell !== undefined && tables.colors[cell.tp][cell.col] !== black) {

      // Update highlighted cells (i.e. the ones who appear after a click)
      let children = [];

      // Update cells (show hidden verdicts after a click)
      let cloneColorsTable = [...tables.colors];

      for (let i = 0; i < cell.cells.length; ++i) {
        cloneColorsTable[cell.cells[i].tp][cell.cells[i].col] = cellColor(cell.cells[i].bool);
        children.push({ tp: cell.cells[i].tp, col: cell.cells[i].col + columns.preds.length, isHighlighted: false });
      }

      // Update header highlights
      let newSubfsHeaderHighlights = getHeaderHighlights(colGridIndex - columns.preds.length,
                                                         columns.subfsScopes,
                                                         subfsGridColumns.length);

      // Update other highlights
      let newHighlights = updateHighlights(ts, tp, colGridIndex, cell, objs.dbs, highlights,
                                           newSubfsHeaderHighlights, children);

      // Update state
      let action;

      if (cell.kind === "assignment") {
        action = { type: "updateTable",
                   colorsTable: cloneColorsTable,
                   selectedRows: newHighlights.selectedRows,
                   highlightedCells: newHighlights.highlightedCells,
                   pathsMap: newHighlights.clonePathsMap,
                   subfsHeader: newSubfsHeaderHighlights,
                   hoversTable: updateHovers([cell.var], [cell.value], colGridIndex - columns.preds.length, columns.subfsScopes, tables.hovers)
                 };
      } else {
        action = { type: "updateTable",
                   colorsTable: cloneColorsTable,
                   selectedRows: newHighlights.selectedRows,
                   highlightedCells: newHighlights.highlightedCells,
                   pathsMap: newHighlights.clonePathsMap,
                   subfsHeader: newSubfsHeaderHighlights };
      }

      setMonitorState(action);
    }
  };

  return (
    <Box height="60vh"
         sx={{
           '& .columnHeader--CurHighlighted': {
             backgroundColor: blueGrey[100],
           },
           '& .columnHeader--LeftHighlighted': {
             backgroundColor: amber[300],
           },
           '& .columnHeader--RightHighlighted': {
             backgroundColor: teal[100],
           },
           '& .cell--LeftHighlighted': {
             backgroundColor: amber[300],
           },
           '& .cell--RightHighlighted': {
             backgroundColor: teal[100],
           },
           '& .cell--PathHighlighted': {
             backgroundColor: blueGrey[100],
           },
           '& .row--Highlighted': {
             bgcolor: amber[50],
             '&:hover': {
               bgcolor: amber[50],
             },
           },
           '& .row--Plain': {
             bgcolor: common.white,
             '&:hover': {
               bgcolor: common.gray,
             },
           },
         }}>
      <DataGrid
        rows={rows}
        columns={predsGridColumns.concat(tptsGridColumns.concat(valuesGridColumn.concat(subfsGridColumns)))}
        getRowClassName={(params) => {
          if (highlights.selectedRows !== undefined &&
              highlights.selectedRows.includes(params.row.tp)) return 'row--Highlighted';
          else return 'row--Plain';
        }}
        getCellClassName={(params) => {

          if (highlights.highlightedCells.length !== 0) {
            for (let i = 0; i < highlights.highlightedCells.length; ++i) {
              if (highlights.highlightedCells[i].tp === params.row.tp &&
                  highlights.highlightedCells[i].col + columns.preds.length === parseInt(params.colDef.field)) {
                if (highlights.highlightedCells[i].type === "leftHighlight") {
                  return 'cell--LeftHighlighted';
                } else {
                  if (highlights.highlightedCells[i].type === "rightHighlight") {
                    return 'cell--RightHighlighted';
                  } else {
                    return '';
                  }
                }
              }
            }
          }

          let m = highlights.pathsMap.get(params.row.tp.toString() + params.colDef.field);
          if (m !== undefined && m.isHighlighted) {
            return 'cell--PathHighlighted';
          }

          return '';

        }}
        componentsProps={{
          cell: {
            onMouseEnter: handlePopoverOpen,
            onMouseLeave: handlePopoverClose
          },
        }}
        pageSize={100}
        rowsPerPageOptions={[100]}
        density="compact"
        disableColumnMenu
        disableSelectionOnClick
      />
      <Popover
        sx={{
          pointerEvents: 'none',
        }}
        open={open}
        anchorEl={anchorEl}
        anchorOrigin={{
          vertical: 'bottom',
          horizontal: 'left',
        }}
        transformOrigin={{
          vertical: 'top',
          horizontal: 'left',
        }}
        onClose={handlePopoverClose}
        disableRestoreFocus
      >
        { anchorValue.kind === "db" && <DbTable db={anchorValue.value}/> }
        { anchorValue.kind === "subf" && <HoverTable table={anchorValue.table} subf={anchorValue.subf}/> }
      </Popover>
    </Box>
  );
}

export default TimeGrid;
