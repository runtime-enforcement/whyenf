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
      if (j === 0) squares[tp][columns[j]] = squareColor(mockData.explanations[tp].explanation.type);
      else squares[tp][columns[j]] = "primary";
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
      renderCell: (params) => <Square value={squares[params.row.tp][params.colDef.field]}
                                      onClick={() => handleClick(params.row.tp, params.colDef.field)} />,
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
      renderCell: () => <Square value="primary" />,
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

  const handleClick = (tp, formString) => {
    let newSquares = squares.slice();
    setSquares({ squares: updateSquares(mockData.explanations[tp].explanation, mockData.subformulas, newSquares) });
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
