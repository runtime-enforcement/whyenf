import React, { useState } from 'react';
import Box from '@mui/material/Box';
import { DataGrid } from '@mui/x-data-grid';
import Button from '@mui/material/Button';
import CircleIcon from '@mui/icons-material/Circle';
import CancelIcon from '@mui/icons-material/Cancel';
import CheckCircleIcon from '@mui/icons-material/CheckCircle';
import DetailsIcon from '@mui/icons-material/Details';
import StorageIcon from '@mui/icons-material/Storage';
import Popover from '@mui/material/Popover';
import Typography from '@mui/material/Typography';
import { red, amber, lightGreen, indigo } from '@mui/material/colors';
import { common } from '@mui/material/colors';
import { black, squareColor, cellColor, tpsIn } from '../util';
import MenuCell from './MenuCell';
import DbTable from './DbTable';

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
                     setMonitorState }) {

  const [anchorEl, setAnchorEl] = useState(null);
  const [anchorValue, setAnchorValue] = useState({});
  const open = Boolean(anchorEl);

  const handlePopoverOpen = (event) => {
    const row = event.currentTarget.parentElement.dataset.id;
    const col = parseInt(event.currentTarget.dataset.field);

    // Preds
    if (col < objs.dbs.nCols && tables.dbs[row][col].length !== 0) {
      setAnchorValue({ kind: "db", value: tables.dbs[row][col] });
      setAnchorEl(event.currentTarget);
    }

    // Subformulas
    if (col >= columns.preds.length &&
        tables.colors[row][col - columns.preds.length] !== "" &&
        tables.colors[row][col - columns.preds.length] !== black &&
        tables.cells[row][col - columns.preds.length].kind !== undefined &&
        tables.cells[row][col - columns.preds.length].kind !== "partition") {
      setAnchorValue({ kind: "subf", value: subformulas[col - columns.preds.length] });
      setAnchorEl(event.currentTarget);
    }
  };

  const handlePopoverClose = () => {
    setAnchorEl(null);
  };

  // Preds columns
  const predsWidth = columns.preds.reduce ((acc, pred) =>
    Math.max(acc, (10*(pred.length))), 50
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
      disableClickEventBubbling: true
    }));

  // TP/TS columns
  const tsWidth = objs.dbs.reduce ((acc, { ts, tp }) =>
    Math.max(acc, (10*(ts.toString().length))), 50
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
        return <MenuCell explObj={objs.expls[params.id].expl}
                         colorsTable={tables.colors}
                         cellsTable={tables.cells}
                         curCol={0}
                         setMonitorState={setMonitorState} />;
      }
    }
  ];

  // Subfs columns
  const subfsWidth = columns.subfs.reduce((acc, subf) =>
    Math.max(acc, (9*(subf.length))), 60
  );

  const subfsGridColumns = columns.subfs.slice(0).map((f, i) =>
    ({
      field: (i+columns.preds.length).toString(),
      headerName: f,
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
                             curCol={i}
                             setMonitorState={setMonitorState} />;
          } else {
            return <BoolCell value={tables.colors[params.row.tp][i]}
                             onClick={() => handleClick(params.row.ts, params.row.tp, params.colDef.field)}
                   />;
          }
        } else {
          return <BoolCell value={tables.colors[params.row.tp][i]}
                           onClick={() => handleClick(params.row.ts, params.row.tp, params.colDef.field)}
                 />;
        }
      },
      headerAlign: 'center',
      align: 'center',
      disableClickEventBubbling: true
    }));

  const rows = objs.dbs.map(({ ts, tp }) =>
    ({
      id: tp,
      tp: tp,
      ts: ts
    }));

  const handleClick = (ts, tp, col) => {

    const colIndex = parseInt(col);

    let cell = tables.cells[tp][colIndex - columns.preds.length];

    if (cell !== undefined && tables.colors[cell.tp][cell.col] !== black) {

      // Update highlighted cells (i.e. the ones who appear after a click)
      let highlightedCells = [];
      let children = [];

      // Update cells (show hidden verdicts after a click)
      let cloneColorsTable = [...tables.colors];

      for (let i = 0; i < cell.cells.length; ++i) {
        cloneColorsTable[cell.cells[i].tp][cell.cells[i].col] = cellColor(cell.cells[i].bool);
        highlightedCells.push({ tp: cell.cells[i].tp, col: cell.cells[i].col });
        children.push({ tp: cell.cells[i].tp, col: cell.cells[i].col + columns.preds.length, isHighlighted: false });
      }

      // Update interval highlighting
      let lastTS = objs.dbs[objs.dbs.length - 1].ts;
      let selRows = (cell.interval !== undefined) ? tpsIn(ts, tp, cell.interval, cell.period, lastTS, objs.dbs) : [];

      // Update (potentially multiple) open paths to be highlighted
      let clonePathsMap = new Map(highlights.pathsMap);

      for (const [k, obj] of clonePathsMap) {
        if (obj.isHighlighted) clonePathsMap.set(k, {...obj, isHighlighted: false });
      }

      for (let i = 0; i < children.length; ++i) {
        clonePathsMap.set(children[i].tp.toString() + children[i].col.toString(),
                          { parent: tp.toString() + colIndex.toString(),
                            isHighlighted: false,
                            tp: children[i].tp, col: children[i].col });
      }

      let cur = clonePathsMap.get(tp.toString() + colIndex.toString());

      if (cur === undefined) {
        clonePathsMap.set(tp.toString() + colIndex.toString(),
                          { parent: null,
                            isHighlighted: true,
                            tp: tp,
                            col: colIndex });
      } else {
        clonePathsMap.set(tp.toString() + colIndex.toString(),
                          {...cur, isHighlighted: true });
      }

      if (cur !== undefined) {
        while (cur.parent !== null) {
          cur = clonePathsMap.get(cur.parent);
          clonePathsMap.set(cur, {...cur, isHighlighted: true });
        }
      }

      let action = { type: "updateTable",
                     colorsTable: cloneColorsTable,
                     selectedRows: selRows,
                     highlightedCells: highlightedCells,
                     pathsMap: clonePathsMap };
      setMonitorState(action);
    }
  };

  return (
    <Box height="60vh"
         sx={{
           '& .cell--Highlighted': {
             backgroundColor: amber[300],
           },
           '& .cell--PathHighlighted': {
             backgroundColor: indigo[100],
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
          if (highlights.selectedRows.includes(params.row.tp)) return 'row--Highlighted';
          else return 'row--Plain';
        }}
        getCellClassName={(params) => {

          if (highlights.highlightedCells.length !== 0) {
            for (let i = 0; i < highlights.highlightedCells.length; ++i) {
              if (highlights.highlightedCells[i].tp === params.row.tp
                  && highlights.highlightedCells[i].col + columns.preds.length === parseInt(params.colDef.field))
                return 'cell--Highlighted';
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
            onMouseLeave: handlePopoverClose,
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
        { anchorValue.kind === "subf" && <Typography sx={{ p: 1 }}>{anchorValue.value}</Typography> }
      </Popover>
    </Box>
  );
}

export default TimeGrid;
