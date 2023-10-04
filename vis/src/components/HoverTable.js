import * as React from 'react';
import Table from '@mui/material/Table';
import TableBody from '@mui/material/TableBody';
import TableCell from '@mui/material/TableCell';
import TableContainer from '@mui/material/TableContainer';
import TableHead from '@mui/material/TableHead';
import TableRow from '@mui/material/TableRow';
import Paper from '@mui/material/Paper';

export default function HoverTable({ table, subf }) {

  return (
    <div className="muiTable">
      <TableContainer component={Paper}>
        <Table size="small" aria-label="a dense table">
          <TableHead>
            <TableRow>
              {table.columns.map((v, i) =>
                <TableCell key={i} align="center">
                  <span style={{fontWeight: 'bold'}}>
                    {v}
                  </span>
                </TableCell>
              )}
              <TableCell key={table.columns.length + 1} align="center">
                <span style={{fontWeight: 'bold'}}>
                  Formula
                </span>
              </TableCell>
            </TableRow>
          </TableHead>
          <TableBody>
            <TableRow>
              {table.values.map((v, i) =>
                <TableCell key={i}>
                  {v}
                </TableCell>
              )}
              <TableCell key={table.values.length + 1}>
                {subf}
              </TableCell>
            </TableRow>
          </TableBody>
        </Table>
      </TableContainer>
    </div>
  );
}
