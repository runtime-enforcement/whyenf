import * as React from 'react';
import Table from '@mui/material/Table';
import TableBody from '@mui/material/TableBody';
import TableCell from '@mui/material/TableCell';
import TableContainer from '@mui/material/TableContainer';
import TableHead from '@mui/material/TableHead';
import TableRow from '@mui/material/TableRow';
import Paper from '@mui/material/Paper';

export default function DenseTable( { db } ) {

  const vars = [...new Set(db.map(a => a.var))];

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
