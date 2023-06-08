import React, { useState } from 'react';
import Box from '@mui/material/Box';
import { DataGrid } from '@mui/x-data-grid';
import Button from '@mui/material/Button';
import CircleIcon from '@mui/icons-material/Circle';
import CancelIcon from '@mui/icons-material/Cancel';
import CheckCircleIcon from '@mui/icons-material/CheckCircle';
import Popover from '@mui/material/Popover';
import Typography from '@mui/material/Typography';
import { red, amber, lightGreen, indigo } from '@mui/material/colors';
import { common } from '@mui/material/colors';
import { black,
         squareColor,
         tpsIn } from '../util';

function Cell(props) {
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

function TimeGrid ({ explObjs,
                     dbsObjs,
                     dbsColumns,
                     subfsColumns,
                     subformulas,
                     squares,
                     selectedRows,
                     highlightedCells,
                     pathsMap,
                     setMonitorState }) {

  const [anchorEl, setAnchorEl] = useState(null);
  const [value, setValue] = useState('');
  const open = Boolean(anchorEl);

  const handlePopoverOpen = (event) => {
    const col = parseInt(event.currentTarget.dataset.field);
    const row = event.currentTarget.parentElement.dataset.id;
    if (col >= dbsColumns.length && squares[row][col] !== "" && squares[row][col] !== black) {
      if (value !== subformulas[col - dbsColumns.length]) setValue(subformulas[col - dbsColumns.length]);
      setAnchorEl(event.currentTarget);
    }
  };

  const handlePopoverClose = () => {
    setAnchorEl(null);
  };

  const apsWidth = dbsColumns.reduce(
    (acc, ap) => Math.max(acc, (8*(ap.length))),
    50
  );

  const apsGridColumns = dbsColumns.slice(0).map((a, i) =>
    ({
      field: i.toString(),
      headerName: a,
      width: apsWidth,
      sortable: false,
      renderHeader: () => a,
      renderCell: (params) => <Cell value={squares[params.row.tp][i]} />,
      headerAlign: 'center',
      align: 'center',
      disableClickEventBubbling: true
    }));

  const fixedGridColumns = [
    {
      field: 'tp',
      headerName: <b>TP</b>,
      width: 60,
      sortable: false,
      headerAlign: 'center',
      align: 'center',
      disableClickEventBubbling: true
    },
    { field: 'ts',
      headerName: <b>TS</b>,
      width: 60,
      sortable: false,
      headerAlign: 'center',
      align: 'center',
      disableClickEventBubbling: true
    }
  ];

  const subfsWidth = subfsColumns.reduce(
    (acc, ap) => Math.max(acc, (8*(ap.length))),
    60
  );

  const subfsGridColumns = subfsColumns.slice(0).map((f, i) =>
    ({
      field: (i+dbsColumns.length).toString(),
      headerName: f,
      width: subfsWidth,
      sortable: false,
      renderHeader: () => f,
      renderCell: (params) => { return <Cell value={squares[params.row.tp][i+dbsColumns.length]}
                                             onClick={() => handleClick(params.row.ts, params.row.tp, params.colDef.field)} />; },
      headerAlign: 'center',
      align: 'center',
      disableClickEventBubbling: true
    }));

  console.log(dbsObjs);

  const rows = dbsObjs.map(({ ts, tp }) =>
    ({
      id: tp,
      tp: tp,
      ts: ts
    }));

  const handleClick = (ts, tp, col) => {
    const colIndex = parseInt(col);

    let cloneSquares = [...squares];
    let clonePathsMap = new Map(pathsMap);
    let cell;

    for (let i = 0; i < explObjs.length; ++i) {
      let c = explObjs[i].table.find(c => c.tp === tp && c.col === colIndex);
      if (c !== undefined) cell = c;
    }

    if (cell !== undefined && squares[cell.tp][cell.col] !== black && cell.cells.length !== 0) {
      // Update highlighted cells (i.e. the ones who appear after a click)
      let highlightedCells = [];
      let children = [];

      // Update cells (show hidden verdicts after a click)
      for (let i = 0; i < cell.cells.length; ++i) {
        cloneSquares[cell.cells[i].tp][cell.cells[i].col] = squareColor(cell.cells[i].bool);
        highlightedCells.push({ tp: cell.cells[i].tp, col: cell.cells[i].col });
        children.push({ tp: cell.cells[i].tp, col: cell.cells[i].col, isHighlighted: false });
      }

      // Update interval highlighting
      let lastTS = dbsObjs[dbsObjs.length - 1].ts;
      let selRows = (cell.interval !== undefined) ? tpsIn(ts, tp, cell.interval, cell.period, lastTS, dbsObjs) : [];

      // Update (potentially multiple) open paths to be highlighted
      for (const [k, obj] of pathsMap) {
        if (obj.isHighlighted) clonePathsMap.set(k, {...obj, isHighlighted: false });
      }

      for (let i = 0; i < children.length; ++i) {
        clonePathsMap.set(children[i].tp.toString() + children[i].col.toString(),
                          { parent: tp.toString() + colIndex.toString(), isHighlighted: false,
                            tp: children[i].tp, col: children[i].col });
      }

      let cur = clonePathsMap.get(tp.toString() + colIndex.toString());
      if (cur === undefined) clonePathsMap.set(tp.toString() + colIndex.toString(),
                                               { parent: null, isHighlighted: true, tp: tp, col: colIndex });
      else clonePathsMap.set(tp.toString() + colIndex.toString(), {...cur, isHighlighted: true });

      if (cur !== undefined) {
        while (cur.parent !== null) {
          cur = clonePathsMap.get(cur.parent);
          clonePathsMap.set(cur, {...cur, isHighlighted: true });
        }
      }

      let action = { type: "updateTable",
                     squares: cloneSquares,
                     selectedRows: selRows,
                     highlightedCells: highlightedCells,
                     pathsMap: clonePathsMap,
                   };
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
        columns={apsGridColumns.concat(fixedGridColumns.concat(subfsGridColumns))}
        getRowClassName={(params) => {
          if (selectedRows.includes(params.row.tp)) return 'row--Highlighted';
          else return 'row--Plain';
        }}
        getCellClassName={(params) => {
          if (highlightedCells.length !== 0) {
            for (let i = 0; i < highlightedCells.length; ++i) {
              if (highlightedCells[i].tp === params.row.tp
                  && highlightedCells[i].col === parseInt(params.colDef.field))
                return 'cell--Highlighted';
            }
          }
          for (const [k, obj] of pathsMap) {
            if (obj.isHighlighted && obj.tp === params.row.tp && obj.col === parseInt(params.colDef.field))
              return 'cell--PathHighlighted';
          }
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
        <Typography sx={{ p: 1 }}>{value}</Typography>
      </Popover>
    </Box>
  );
}

export default TimeGrid;
