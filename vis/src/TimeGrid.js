import React, { useState } from "react";
import Box from '@mui/material/Box';
import { DataGrid } from '@mui/x-data-grid';
import Button from '@mui/material/Button';
import SquareIcon from '@mui/icons-material/Square';
import { squareColor, squareColorTest } from './util';

function Square(props) {
  return (
    <Button onClick={props.onClick}>
      <SquareIcon style={{ color: props.value }} />
    </Button>
  );
}

function TimeGrid ({ explanations, columns, squares, dispatch }) {

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
    }
  ];

  const dynamicColumns = columns.slice(0).map((f, i) =>
    ({
      field: i.toString(),
      headerName: f,
      width: (10*(f.length)),
      sortable: false,
      renderHeader: () => columns[i],
      renderCell: (params) => <Square value={squares[params.row.tp][i]}
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

    let action = { squares: cloneSquares, type: 'update' };
    dispatch(action);
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
