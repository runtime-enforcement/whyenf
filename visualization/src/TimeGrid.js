import React, { useState } from 'react';
import Box from '@mui/material/Box';
import { DataGrid } from '@mui/x-data-grid';
import { mockData } from './data';
import { pickColumnItem } from './util';
import SquareIcon from '@mui/icons-material/Square';

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
    field: "f0",
    headerName: mockData.formula,
    width: 50,
    sortable: false,
    renderHeader: () => pickColumnItem(0),
    renderCell: () => <SquareIcon />,
    headerAlign: 'center',
    align: 'center',
    disableClickEventBubbling: true
  }
];

const dynamicColumns = mockData.subformulas.map((f, i) =>
  ({
    field: "f".concat((i+1).toString()),
    headerName: f,
    width: 50,
    sortable: false,
    renderHeader: () => pickColumnItem(i+1),
    renderCell: () => <SquareIcon />,
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

function TimeGrid () {
  const [selectedCell, setSelectedCell] = useState({});
  const [openDialog, setOpenDialog] = useState(false);

  function currentlySelected(params: GridCellParams) {
    const value = params.colDef.field;
    // const api: GridApi = params.api;

    if (value === "tp" || value === "ts") return;

    console.log(params);

    // const fields = api
    //       .getAllColumns()
    //       .map((c) => c.field)
    //       .filter((c) => c !== "__check__" && !!c);
    // const thisRow: Record<string, GridCellValue> = {};

    // fields.forEach((f) => {
    //   thisRow[f] = params.getValue(params.id, f);
    // });

    // const user = {};
    // user["id"] = Number(thisRow["id"]);
    // user["name"] = thisRow["name"]!.toString();
    // user["surname"] = thisRow["surname"]!.toString();

    // setSelectedUser(user);
    setOpenDialog(true);
  }

  const handleClose = () => {
    setOpenDialog(false);
  };

  return (
    <Box sx={{ height: 585 }}>
      <DataGrid
        rows={rows}
        columns={fixedColumns.concat(dynamicColumns)}
        pageSize={13}
        rowsPerPageOptions={[5]}
        onCellClick={currentlySelected}
        density="compact"
        disableColumnMenu
      />
    </Box>
  );
}

export default TimeGrid;
