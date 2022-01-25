import * as React from 'react';
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
    align: 'center'
  },
  { field: 'ts',
    headerName: 'TS',
    width: 50,
    sortable: false,
    align: 'center'
  },
  {
    field: "f0",
    headerName: mockData.formula,
    width: 50,
    sortable: false,
    renderHeader: () => pickColumnItem(0),
    renderCell: () => <SquareIcon />,
    headerAlign: 'center',
    align: 'center'
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
    align: 'center'
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


export default class TimeGrid extends React.Component {
  render() {
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
}
