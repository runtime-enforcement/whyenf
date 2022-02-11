import React, { useState, useEffect } from "react";
import Box from '@mui/material/Box';
import { DataGrid } from '@mui/x-data-grid';
import Button from '@mui/material/Button';
import SquareIcon from '@mui/icons-material/Square';
import { pickColumnItem, squareColor, updateSquares } from './util';

let mockData = require('./data.json');
console.log(mockData);

function Square(props) {
  return (
    <Button onClick={props.onClick}>
      <SquareIcon style={{ color: props.value }} />
    </Button>
  );
}

function initSquares(explanationsLength, columns) {
  var squares = [];
  for (let tp = 0; tp < explanationsLength; ++tp) {
    squares[tp] = {};
    for (let j = 0; j < columns.length; ++j) {
      if (j === 0) squares[tp][j] = squareColor(mockData.explanations[tp].explanation.type);
      else squares[tp][j] = "primary";
    }
  }
  return squares;
}

function TimeGrid () {
  let sq = initSquares(mockData.explanations.length, mockData.columns);

  const [squares, setSquares] = React.useState(sq);

  const fixedColumns = [
    {
      field: 'tp',
      headerName: 'TP',
      width: 50,
      sortable: false,
      align: 'center',
      disableClickEventBubbling: true
    },
    { field: 'ts',
      headerName: 'TS',
      width: 50,
      sortable: false,
      align: 'center',
      disableClickEventBubbling: true
    },
    {
      field: mockData.columns[0],
      headerName: mockData.columns[0],
      width: 50,
      sortable: false,
      renderHeader: () => pickColumnItem(0),
      renderCell: (params) => <Square value={squares[params.row.tp][0]}
                                      onClick={() => handleClick(params, params.row.tp, params.colDef.field)} />,
      headerAlign: 'center',
      align: 'center',
      disableClickEventBubbling: true
    }
  ];

  const dynamicColumns = mockData.columns.slice(1).map((f, i) =>
    ({
      field: f,
      headerName: f,
      width: 50,
      sortable: false,
      renderHeader: () => pickColumnItem(i+1),
      renderCell: (params) => <Square value={squares[params.row.tp][i+1]} />,
      headerAlign: 'center',
      align: 'center',
      disableClickEventBubbling: true
    }));

  const rows = mockData.explanations.map((p, i) =>
    ({
      id: i,
      tp: p.tp,
      ts: p.ts,
      f0: "",
      f1: "",
      f2: "",
      f3: ""
    }));

  const handleClick = (params, tp, formString) => {
    let newSquares = squares.slice();
    newSquares = updateSquares(mockData.explanations[tp].explanation, mockData.subformulas, newSquares);
    setSquares(sq);
    setSquares(newSquares);
  };

  const renderSquare = (tp, formString) => {
    return (
      <Square
        value={squares[tp][formString]}
        onClick={() => handleClick(tp, formString)}
      />
    );
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
