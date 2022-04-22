import React, { useState } from "react";
import Box from '@mui/material/Box';
import { DataGrid } from '@mui/x-data-grid';
import Button from '@mui/material/Button';
import CircleIcon from '@mui/icons-material/Circle';
import CancelIcon from '@mui/icons-material/Cancel';
import CheckCircleIcon from '@mui/icons-material/CheckCircle';
import { red, purple, yellow, lightGreen, cyan } from '@mui/material/colors';
import { common } from '@mui/material/colors'
import { squareColor, squareColorTest, tpsIn } from './util';

function Cell(props) {
  return (
    <Button onClick={props.onClick}>
      { props.value === "" && <CircleIcon /> }
      { props.value === red[500] && <CancelIcon style={{ color: props.value }} /> }
      { props.value === lightGreen[500] && <CheckCircleIcon style={{ color: props.value }} /> }
    </Button>
  );
}

function TimeGrid ({ explanations, atoms, apsColumns, subfsColumns, squares, selectedRows, dispatch }) {

  const apsGridColumns = apsColumns.slice(0).map((a, i) =>
    ({
      field: i.toString(),
      headerName: a,
      width: (10*(a.length)),
      sortable: false,
      renderHeader: () => apsColumns[i],
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
      align: 'center',
      disableClickEventBubbling: true
    },
    { field: 'ts',
      headerName: 'TS',
      width: 55,
      sortable: false,
      align: 'center',
      disableClickEventBubbling: true
    }
  ];

  const subfsGridColumns = subfsColumns.slice(0).map((f, i) =>
    ({
      field: (i+apsColumns.length).toString(),
      headerName: f,
      width: (10*(f.length)),
      sortable: false,
      renderHeader: () => subfsColumns[i],
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

    if (cell !== undefined && squares[cell.tp][cell.col] !== "") {
      for (let i = 0; i < cell.cells.length; ++i) {
        cloneSquares[cell.cells[i].tp][cell.cells[i].col] = squareColor(cell.cells[i].bool);
      }

      let selRows = tpsIn(ts, tp, cell.interval, cell.period, atoms);

      let action = { type: "updateTable",
                     squares: cloneSquares,
                     selectedRows: selRows
                   };

      dispatch(action);
    }
  };

  return (
    <Box sx={{ height: 585,
               '& .cell--Highlighted': {
                 backgroundColor: purple[300],
               },
               '& .row--Highlighted': {
                 bgcolor: cyan[100],
                 '&:hover': {
                   bgcolor: cyan[200],
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
          if (selectedRows.includes(params.row.tp)) return `row--Highlighted`
          else return `row--Plain` }}
        pageSize={13}
        rowsPerPageOptions={[5]}
        density="compact"
        disableColumnMenu
        disableSelectionOnClick
      />
    </Box>
  );
}

export default TimeGrid;
