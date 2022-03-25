import React, { useState, useEffect } from "react";
import Box from '@mui/material/Box';
import { DataGrid } from '@mui/x-data-grid';
import Button from '@mui/material/Button';
import SquareIcon from '@mui/icons-material/Square';
import { squareColor, squareColorTest } from './util';

let mockData = require('./data.json');
// console.log(mockData);

function Square(props) {
  return (
    <Button onClick={props.onClick}>
      <SquareIcon style={{ color: props.value }} />
    </Button>
  );
}

function initSquares(explanations) {
  var squares = [];
  for (let tp = 0; tp < explanations.length; ++tp) {
    let tbl = explanations[tp].table;
    squares[tp] = [];
    console.log(tbl);
    for (let j = 0; j < tbl.length; ++j) {
      if (tp === tbl[j].tp) {
        switch(tbl[j].bool) {
        case true:
          squares[tp][tbl[j].col] = squareColor(true);
          break;
        case false:
          squares[tp][tbl[j].col] = squareColor(false);
          break;
        default:
          squares[tp][tbl[j].col] = "primary";
          break;
        }
      }
    }
  }
  return squares;
}

function TimeGrid ({ checker, measure, formula, trace }) {
  const [explanations, setExplanations] = React.useState(JSON.parse(window.monitor(trace, checker, measure, formula)[2]));
  const [columns, setColumns] = React.useState((JSON.parse(window.getColumns(formula))).columns);
  const [squares, setSquares] = React.useState(initSquares(explanations));
  console.log(columns);
  console.log(explanations);
  console.log(squares);

  const fixedColumns = [
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
    },
    {
      field: "0",
      headerName: columns[0],
      width: (10*(columns[0].length)),
      sortable: false,
      renderHeader: () => columns[0],
      renderCell: (params) => <Square value={squares[params.row.tp][0]}
                                      onClick={() => handleClick(params, params.row.tp, params.colDef.field)} />,
      headerAlign: 'center',
      align: 'center',
      disableClickEventBubbling: true
    }
  ];

  const dynamicColumns = columns.slice(1).map((f, i) =>
    ({
      field: (i+1).toString(),
      headerName: f,
      width: (10*(f.length)),
      sortable: false,
      renderHeader: () => columns[i+1],
      renderCell: (params) => <Square value={squares[params.row.tp][i+1]}
                                      onClick={() => handleClick(params, params.row.tp, params.colDef.field)} />,
      headerAlign: 'center',
      align: 'center',
      disableClickEventBubbling: true
    }));

  const rows = explanations.map(({ ts, tp }) =>
    ({
      id: tp,
      tp: tp,
      ts: ts
    }));

  const handleClick = (params, tp, col) => {
    const colIndex = parseInt(col);
    const cloneSquares = [...squares];

    const cell = explanations[tp].table.find(c => c.tp === tp && c.col === colIndex);
    for (let i = 0; i < cell.cells.length; ++i) {
      cloneSquares[cell.cells[i].tp][cell.cells[i].col] = squareColorTest(cell.cells[i].bool);
    }

    setSquares(cloneSquares);
  };

  return (
    <Box sx={{ height: 585 }}>
      <DataGrid
        rows={rows}
        columns={fixedColumns.concat(dynamicColumns)}
        pageSize={13}
        rowsPerPageOptions={[5]}
        density="compact"
        disableColumnMenu
      />
    </Box>
  );
}

export default TimeGrid;
