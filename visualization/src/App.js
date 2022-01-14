import * as React from 'react';
import { DataGrid } from '@mui/x-data-grid';

const columns = [
  { field: 'id', headerName: 'ID', width: 20 },
  { field: 'ts0', headerName: '0', width: 20 },
  { field: 'ts1', headerName: '1', width: 20 },
  { field: 'ts2', headerName: '2', width: 20 },
  { field: 'ts3', headerName: '3', width: 20 },
  { field: 'ts4', headerName: '4', width: 20 },
  // { field: 'firstName', headerName: 'First name', width: 130 },
  // { field: 'ts0', headerName: 'Last name', width: 130 },
  // {
  //   field: 'age',
  //   headerName: 'Age',
  //   type: 'number',
  //   width: 90,
  // },
  // {
  //   field: 'fullName',
  //   headerName: 'Full name',
  //   description: 'This column has a value getter and is not sortable.',
  //   sortable: false,
  //   width: 160,
  //   valueGetter: (params) =>
  //     `${params.getValue(params.id, 'firstName') || ''} ${
  //       params.getValue(params.id, 'ts0') || ''
  //     }`,
  // },
];

const rows = [
  { id: 1, ts0: 'Snow', ts1: 'Jon', ts2: 35 },
  { id: 2, ts0: 'Lannister', ts1: 'Cersei', ts2: 42 },
  { id: 3, ts0: 'Lannister', ts1: 'Jaime', ts2: 45 },
  { id: 4, ts0: 'Stark', ts1: 'Arya', ts2: 16 },
  { id: 5, ts0: 'Targaryen', ts1: 'Daenerys', ts2: null },
  { id: 6, ts0: 'Melisandre', ts1: null, ts2: 150 },
  { id: 7, ts0: 'Clifford', ts1: 'Ferrara', ts2: 44 },
  { id: 8, ts0: 'Frances', ts1: 'Rossini', ts2: 36 },
  { id: 9, ts0: 'Roxie', ts1: 'Harvey', ts2: 65 },
];

export default function DataTable() {
  return (
    <div style={{ height: 400, width: '100%' }}>
      <DataGrid
        rows={rows}
        columns={columns}
        pageSize={5}
        rowsPerPageOptions={[5]}
        checkboxSelection
      />
    </div>
  );
}
