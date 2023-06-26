import * as React from 'react';
import Table from '@mui/material/Table';
import TableBody from '@mui/material/TableBody';
import TableCell from '@mui/material/TableCell';
import TableContainer from '@mui/material/TableContainer';
import TableHead from '@mui/material/TableHead';
import TableRow from '@mui/material/TableRow';
import Paper from '@mui/material/Paper';

function createData(name, calories, fat, carbs, protein) {
  return { name, calories, fat, carbs, protein };
}

const rows = [
  createData('Frozen yoghurt', 159, 6.0, 24, 4.0),
  createData('Ice cream sandwich', 237, 9.0, 37, 4.3),
  createData('Eclair', 262, 16.0, 24, 6.0),
  createData('Cupcake', 305, 3.7, 67, 4.3),
  createData('Gingerbread', 356, 16.0, 49, 3.9),
];

export default function DenseTable( { db } ) {

  const vars = [... new Set(db.map(a => a.var))];

  const allValues = db.map(a => a.value);
  const maxCol = vars.length;
  const values = [];

  for (let i = 0; i < allValues.length; i += maxCol) {
    values.push(allValues.slice(i, i + maxCol));
  }

  return (
    <div className="muiTable">
      <TableContainer component={Paper}>
        <Table size="small" aria-label="a dense table">
          <TableHead>
            <TableRow>
              {vars.map((v, i) =>
                <TableCell key={i} align="center">
                  <span style={{fontWeight: 'bold'}}>
                    {v}
                  </span>
                </TableCell>
              )}
            </TableRow>
          </TableHead>
          <TableBody>
            {values.map((row, i) => (
              <TableRow key={i}>
                { row.map((v, j) =>
                  <TableCell key={j}>
                    {v}
                  </TableCell>
                )}
              </TableRow>
            ))}
          </TableBody>
        </Table>
      </TableContainer>
    </div>
  );
}
