import { red, lightGreen } from '@mui/material/colors';

export const black = "#000000";

export function cellColor(bool) {
  return (bool ? lightGreen[500] : red[500]);
}

export function computeDbsTable(dbsObjs, nCols, cells = []) {

  let maxRow = dbsObjs.length;
  let maxCol = nCols;

  cells = (cells.length === 0) ? new Array(maxRow).fill(null).map(() => Array(maxCol).fill("")) : cells;

  // Populate cells with dbs
  for (let tp = 0; tp < maxRow; ++tp) {
    let dbs = dbsObjs[tp].dbs_row;
    for (let j = 0; j < maxCol; ++j) {
      if (tp === dbs[j].tp) cells[tp][j] = dbs[j].db;
    }
  }

  return cells;

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

function computePolarity(pol1, pol2) {
  if ((pol1 === "true" && pol2 === "true") ||
      (pol1 === "" && pol2 === "true") ||
      (pol1 === "true" && pol2 === "")) {
    return "true";
  } else {
    if ((pol1 === "false" && pol2 === "false") ||
        (pol1 === "" && pol2 === "false") ||
        (pol1 === "false" && pol2 === "")) {
      return "false"
    } else {
      return "both"
    }
  }
}

export function getPolarity(explObj, col, pol = "") {

  if (explObj.type === "node" || explObj.kind === "partition") {
    for (let i = 0; i < explObj.part.length; ++i) {
      pol = computePolarity(pol, getPolarity(explObj.part[i], col, pol));
    }
    return pol;
  } else {
    let tbl = explObj.table.find(tbl => tbl.col === col);
    return tbl.bool.toString();
  }

}

export function updateCellsTableMain(selCellsObj, cellsTable) {

  let cellsTableClone = [...cellsTable];

  selCellsObj.table.forEach(cell =>
    cellsTableClone[cell.tp][cell.col] = cell
  );

  return cellsTableClone;
}

export function updateCellsTableQuant(selCellsObj, curCol, cellsTable) {

  let cellsTableClone = [...cellsTable];

  selCellsObj.table
    .filter(cell => cell.col !== curCol)
    .forEach(cell =>
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

export function exposeColorsTableQuant(explObj, nextCol, colorsTable) {

  // Initialize empty matrix
  let colorsTableClone = structuredClone(colorsTable);

  // Expose (as a black cell) the boolean subproofs
  for (let i = 0; i < explObj.table.length; ++i) {
    let tbl = explObj.table[i];
    if (tbl.kind === "boolean") {
      for (let j = 0; j < tbl.cells.length; ++j) {
        colorsTableClone[tbl.cells[j].tp][tbl.cells[j].col] = black;
      }
    }
  }

  // Expose boolean verdict in quantifier subformula column
  let tblIndex = explObj.table.findIndex(tbl => tbl.col === nextCol);
  let tbl = explObj.table[tblIndex];
  colorsTableClone[tbl.tp][tbl.col] = tbl.bool ? cellColor(true) : cellColor(false);

  return colorsTableClone;

}

export function exposeColorsTableMain(explObj, maxRow, maxCol) {

  // Initialize empty matrix
  let colorsTable = new Array(maxRow).fill(null).map(() => Array(maxCol).fill(""));

  // Expose (as a black cell) the boolean subproofs
  for (let i = 0; i < explObj.table.length; ++i) {
    let tbl = explObj.table[i];
    if (tbl.kind === "boolean") {
      for (let j = 0; j < tbl.cells.length; ++j) {
        colorsTable[tbl.cells[j].tp][tbl.cells[j].col] = black;
      }
    }
  }

  // Expose boolean verdict in main subformula column
  let tblIndex = explObj.table.findIndex(tbl => tbl.col === 0);
  let tbl = explObj.table[tblIndex];
  colorsTable[tbl.tp][tbl.col] = tbl.bool ? cellColor(true) : cellColor(false);

  return colorsTable;

}

export function updateHighlights(ts, tp, col, cell, dbsObjs, highlights, children) {

  // Update cell highlighting
  let highlightedCells = [];

  for (let i = 0; i < cell.cells.length; ++i) {
    highlightedCells.push({ tp: cell.cells[i].tp, col: cell.cells[i].col });
  }

  // Update interval highlighting
  let lastTS = dbsObjs[dbsObjs.length - 1].ts;
  let selRows = (cell.interval !== undefined) ? tpsIn(ts, tp, cell.interval, cell.period, lastTS, dbsObjs) : [];

  // Update (potentially multiple) open paths to be highlighted
  let clonePathsMap = new Map(highlights.pathsMap);

  for (const [k, obj] of clonePathsMap) {
    if (obj.isHighlighted) clonePathsMap.set(k, {...obj, isHighlighted: false });
  }

  for (let i = 0; i < children.length; ++i) {
    clonePathsMap.set(children[i].tp.toString() + children[i].col.toString(),
                      { parent: tp.toString() + col.toString(),
                        isHighlighted: false,
                        tp: children[i].tp, col: children[i].col });
  }

  let cur = clonePathsMap.get(tp.toString() + col.toString());

  if (cur === undefined) {
    clonePathsMap.set(tp.toString() + col.toString(),
                      { parent: null,
                        isHighlighted: true,
                        tp: tp,
                        col: col });
  } else {
    clonePathsMap.set(tp.toString() + col.toString(),
                      {...cur, isHighlighted: true });
  }

  if (cur !== undefined) {
    while (cur.parent !== null) {
      cur = clonePathsMap.get(cur.parent);
      clonePathsMap.set(cur, {...cur, isHighlighted: true });
    }
  }

  return { selectedRows: selRows,
           highlightedCells: highlightedCells,
           clonePathsMap: clonePathsMap };

}

export function tpsIn(ts, tp, interval, period, lastTS, dbs) {
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

  for (let i = 0; i < dbs.length; ++i) {
    if (dbs[i].ts >= l && dbs[i].ts <= r
        && ((period === "past" && dbs[i].tp <= tp)
            || (period === "future" && dbs[i].tp >= tp))) {
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
