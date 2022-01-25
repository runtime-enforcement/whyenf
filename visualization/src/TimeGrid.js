import * as React from 'react';
import Box from '@mui/material/Box';
import { DataGrid } from '@mui/x-data-grid';
import { mockData } from './data';
import { pickColumnItem } from './util';
import SquareIcon from '@mui/icons-material/Square';
import CropSquareIcon from '@mui/icons-material/CropSquare';
import Filter1Icon from '@mui/icons-material/Filter1';
import Filter2Icon from '@mui/icons-material/Filter2';
import Filter3Icon from '@mui/icons-material/Filter3';
import Filter4Icon from '@mui/icons-material/Filter4';
import Filter5Icon from '@mui/icons-material/Filter5';
import Filter6Icon from '@mui/icons-material/Filter6';
import Filter7Icon from '@mui/icons-material/Filter7';
import Filter8Icon from '@mui/icons-material/Filter8';
import Filter9Icon from '@mui/icons-material/Filter9';

console.log(mockData);

const fixedColumns = [
  {
    field: 'tp',
    headerName: 'TP',
    width: 50,
    sortable: false,
  },
  { field: 'ts',
    headerName: 'TS',
    width: 50,
    sortable: false
  },
];

const dynamicColumns = mockData.subformulas.map((f, i) =>
  ({
    field: i,
    headerName: f,
    width: 50,
    sortable: false,
    renderHeader: () => pickColumnItem(i),
    renderCell: () => <SquareIcon />
  }));

const rows = [
  { id: 1, lastName: 'Snow', firstName: 'Jon', age: 35 },
  { id: 2, lastName: 'Lannister', firstName: 'Cersei', age: 42 },
  { id: 3, lastName: 'Lannister', firstName: 'Jaime', age: 45 },
  { id: 4, lastName: 'Stark', firstName: 'Arya', age: 16 },
  { id: 5, lastName: 'Targaryen', firstName: 'Daenerys', age: null },
  { id: 6, lastName: 'Melisandre', firstName: null, age: 150 },
  { id: 7, lastName: 'Clifford', firstName: 'Ferrara', age: 44 },
  { id: 8, lastName: 'Frances', firstName: 'Rossini', age: 36 },
  { id: 9, lastName: 'Roxie', firstName: 'Harvey', age: 65 },
  { id: 10, lastName: 'Snow', firstName: 'Jon', age: 35 },
  { id: 11, lastName: 'Lannister', firstName: 'Cersei', age: 42 },
  { id: 12, lastName: 'Lannister', firstName: 'Jaime', age: 45 },
  { id: 13, lastName: 'Stark', firstName: 'Arya', age: 16 },
  { id: 14, lastName: 'Targaryen', firstName: 'Daenerys', age: null },
  { id: 15, lastName: 'Melisandre', firstName: null, age: 150 },
  { id: 16, lastName: 'Clifford', firstName: 'Ferrara', age: 44 },
  { id: 17, lastName: 'Frances', firstName: 'Rossini', age: 36 },
  { id: 18, lastName: 'Roxie', firstName: 'Harvey', age: 65 },
];

export default class TimeGrid extends React.Component {
  render() {
    return (
      <Box sx={{ height: 585 }}>
        <DataGrid
          rows={rows}
          columns={fixedColumns.concat(dynamicColumns)}
          pageSize={10}
          rowsPerPageOptions={[5]}
          density="compact"
          disableColumnMenu
        />
      </Box>
    );
  }
}
