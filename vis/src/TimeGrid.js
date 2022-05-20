import React, { useState } from "react";
import Box from '@mui/material/Box';
import { DataGrid } from '@mui/x-data-grid';
import Button from '@mui/material/Button';
import CircleIcon from '@mui/icons-material/Circle';
import CancelIcon from '@mui/icons-material/Cancel';
import CheckCircleIcon from '@mui/icons-material/CheckCircle';
import Popover from '@mui/material/Popover';
import Typography from '@mui/material/Typography';
import { red, amber, lightGreen } from '@mui/material/colors';
import { common } from '@mui/material/colors'
import { black, squareColor, tpsIn, computeMaxCol } from './util';

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

function TimeGrid ({ explanations,
                     atoms,
                     apsColumns,
                     subfsColumns,
                     subformulas,
                     squares,
                     selectedRows,
                     highlightedCells,
                     setMonitorState }) {

  const [anchorEl, setAnchorEl] = React.useState(null);
  const [value, setValue] = React.useState('');
  const open = Boolean(anchorEl);

  const handlePopoverOpen = (event) => {
    const col = parseInt(event.currentTarget.dataset.field);
    const row = event.currentTarget.parentElement.dataset.id;
    if (col >= apsColumns.length && squares[row][col] != "") {
      setValue(subformulas[col - apsColumns.length]);
      setAnchorEl(event.currentTarget);
    }
  };

  const handlePopoverClose = () => {
    setAnchorEl(null);
  };

  const apsGridColumns = apsColumns.slice(0).map((a, i) =>
    ({
      field: i.toString(),
      headerName: a,
      width: (11*(a.length)),
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
      headerName: 'TP',
      width: 55,
      sortable: false,
      headerAlign: 'center',
      align: 'center',
      disableClickEventBubbling: true
    },
    { field: 'ts',
      headerName: 'TS',
      width: 55,
      sortable: false,
      headerAlign: 'center',
      align: 'center',
      disableClickEventBubbling: true
    }
  ];

  const subfsGridColumns = subfsColumns.slice(0).map((f, i) =>
    ({
      field: (i+apsColumns.length).toString(),
      headerName: f,
      width: (11*(f.length)),
      sortable: false,
      renderHeader: () => f,
      renderCell: (params) => { return <Cell value={squares[params.row.tp][i+apsColumns.length]}
                                             onClick={() => handleClick(params.row.ts, params.row.tp, params.colDef.field)} /> },
      headerAlign: 'center',
      align: 'center',
      disableClickEventBubbling: true
    }));

  const rows = atoms.map(({ ts, tp }) =>
    ({
      id: tp,
      tp: tp,
      ts: ts
    }));

  const handleClick = (ts, tp, col) => {
    const colIndex = parseInt(col);
    const cloneSquares = [...squares];
    let cell;

    for (let i = 0; i < explanations.length; ++i) {
      let c = explanations[i].table.find(c => c.tp === tp && c.col === colIndex);
      if (c !== undefined) cell = c;
    }

    if (cell !== undefined && squares[cell.tp][cell.col] !== black && cell.cells.length !== 0) {
      let highlightedCells = [...Array(explanations.length)].map(x=>Array(computeMaxCol(explanations)+1).fill(false));
      for (let i = 0; i < cell.cells.length; ++i) {
        cloneSquares[cell.cells[i].tp][cell.cells[i].col] = squareColor(cell.cells[i].bool);
        highlightedCells[cell.cells[i].tp][cell.cells[i].col] = true;
      }

      let selRows = (cell.interval !== undefined) ? tpsIn(ts, tp, cell.interval, cell.period, atoms) : [];
      let action = { type: "updateTable",
                     squares: cloneSquares,
                     selectedRows: selRows,
                     highlightedCells: highlightedCells
                   };
      setMonitorState(action);
    }
  };

  return (
    <Box sx={{ height: 585,
               '& .cell--Highlighted': {
                 backgroundColor: amber[300],
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
          if (selectedRows.includes(params.row.tp)) return 'row--Highlighted'
          else return 'row--Plain' }}
        getCellClassName={(params) => {
          if (highlightedCells.length !== 0
              && highlightedCells[params.row.tp][parseInt(params.colDef.field)])
            return 'cell--Highlighted';
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
