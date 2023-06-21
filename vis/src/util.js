import { red, lightGreen } from '@mui/material/colors';

export const black = "#000000";

export function cellColor(bool) {
  return (bool ? lightGreen[500] : red[500]);
}

export function computeDbsTable(dbsObjs, cells = []) {

  let maxRow = dbsObjs.length;
  let maxCol = dbsObjs.nCols;

  cells = (cells.length === 0) ? new Array(maxRow).fill(null).map(() => Array(maxCol).fill("")) : cells;

  // Populate cells with dbs
  for (let tp = 0; tp < maxRow; ++tp) {
    let dbs = dbsObjs[tp].dbs_row;
    for (let j = 0; j < maxCol; ++j) {
      if (tp === dbs[j].tp) cells[tp][j] = dbs[j].db.join('\n');
    }
  }

  return cells;

}

export function collectValues(el) {

  let values = [];

  while (el.parentNode) {
    el = el.parentNode;
    if (el.dataset !== undefined && el.dataset.value !== undefined && el.dataset.value.length > 0) {
      values.push(el.dataset.value);
    }
  }

  return values;
}

export function getCells(explObj, path) {

  if (path.length === 0) {
    return explObj;
  } else {

    let subExplObj = explObj.part.find(expl => expl.subset_type === "finite" &&
                                       expl.subset_values.some(val => val === path[0]));

    if (subExplObj === undefined) {
      subExplObj = explObj.part.find(expl => expl.subset_type === "complement");
    }

    path.shift();

    return getCells(subExplObj, path);
  }

}

export function updateCellsTableMain(selCellsObj, cellsTable) {

  let cellsTableClone = [...cellsTable];

  selCellsObj.table.forEach(cell =>
    cellsTableClone[cell.tp][cell.col] = cell
  );

  return cellsTableClone;
}

export function updateCellsTableQuant(selCellsObj, cellsTable) {

  let cellsTableClone = [...cellsTable];

  selCellsObj.cells.forEach(cell =>
    cellsTableClone[cell.tp][cell.col] = cell
  );

  return cellsTableClone;
}

export function initRhsTable(dbsObjs, subfsColumns) {

  let maxRow = dbsObjs.length;
  let maxCol = subfsColumns.length;

  let table = new Array(maxRow).fill(null).map(() => Array(maxCol).fill(""));

  return table;

}

export function exposeColorsTableQuant(explObj, nextCol, maxRow, maxCol, colorsTable) {

  // Initialize empty matrix
  let colorsTableClone = structuredClone(colorsTable);

  console.log(colorsTableClone);

  // Expose boolean verdict in main subformula column
  let tblIndex = explObj.cells.findIndex(tbl => tbl.col === nextCol);
  let tbl = explObj.cells[tblIndex];
  colorsTableClone[tbl.tp][tbl.col] = tbl.bool === "true" ? cellColor(true) : cellColor(false);

  // // Expose (as a black cell) the boolean subproofs
  for (let j = 0; j < explObj.cells.length; ++j) {
    colorsTableClone[explObj.cells[j].tp][explObj.cells[j].col] = black;
  }

  console.log(colorsTableClone);

  return colorsTableClone;

}

export function exposeColorsTableMain(explObj, maxRow, maxCol) {

  // Initialize empty matrix
  let colorsTable = new Array(maxRow).fill(null).map(() => Array(maxCol).fill(""));

  // Expose boolean verdict in main subformula column
  let tblIndex = explObj.table.findIndex(tbl => tbl.col === 0);
  let tbl = explObj.table[tblIndex];
  colorsTable[tbl.tp][tbl.col] = tbl.bool === "true" ? cellColor(true) : cellColor(false);

  // Expose (as a black cell) the boolean subproofs
  for (let i = 0; i < explObj.table.length; ++i) {
    let tbl = explObj.table[i];
    if (tbl.kind === "boolean") {
      for (let j = 0; j < tbl.cells.length; ++j) {
        colorsTable[tbl.cells[j].tp][tbl.cells[j].col] = black;
      }
    }
  }

  return colorsTable;

}

export function tpsIn(ts, tp, interval, period, lastTS, atoms) {
  const i = interval.split(',');
  const a = parseInt(i[0].slice(1));
  const bString = i[1].slice(0, i[1].length-1);

  let idxs = [];
  let b, l, r;

  if (period === "past") {
    if (bString === '∞') {
      l = 0;
      r = ts - a;
    } else {
      b = parseInt(bString);
      l = ts - b;
      r = ts - a;
    }
  } else {
    if (period === "future") {
      if (bString === '∞') {
        l = ts + a;
        r = lastTS;
      } else {
        b = parseInt(bString);
        l = ts + a;
        r = ts + b;
      }
    }
  }

  for (let i = 0; i < atoms.length; ++i) {
    if (atoms[i].ts >= l && atoms[i].ts <= r
        && ((period === "past" && atoms[i].tp <= tp)
            || (period === "future" && atoms[i].tp >= tp))) {
      idxs.push(i);
    }
  }

  return idxs;
}

export function translateError(error) {

  let message;

  if (error.message === undefined && error[1].c !== undefined) {
    message = error[1].c;
  } else {
    if (error.message === undefined && error[1][1].c !== undefined) {
      message = error[1][1].c;
    } else {
      if (error.message !== undefined && error.message.includes("Unexpected token")) {
        message = error.message;
      }
    }
  }

  if (error.message === undefined) {
    switch (message) {
    case "Src.Mtl_parser.MenhirBasics.Error":
        return { name: "Error",
                 message: "Formula could not be parsed.\n\nPlease make sure the syntax is correct."
               };
    case "Src.Monitor.UNBOUNDED_FUTURE":
      return { name: "Error",
               message: "Your formula has an unbounded UNTIL.\n\nPlease make sure all UNTIL instances are bounded."
             };
    case "Src.Monitor.INVALID_TIMESTAMP":
      return { name: "Error",
               message: "Your time-stamps are not monotonically increasing.\n\nPlease rectify your trace and try again."
             };
    default:
      return;
    }
  } else {
    if (error.message !== undefined && error.message.includes("Unexpected token")) {
      return { name: "Error",
               message: "Trace could not be parsed.\n\nPlease make sure the syntax is correct."
             };
    }
  }

  return { name: "Error",
           message: "Something bad happened.\n\nPlease re-check your formula/trace and try again."
         };
}
