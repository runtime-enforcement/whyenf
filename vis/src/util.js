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

export function getExpl(explObj, path) {

  if (path.length === 0) {
    return explObj;
  } else {

    let subExplObj = explObj.part.find(expl => expl.subset_type === "finite" &&
                                       expl.subset_values.some(val => val === path[0]));

    if (subExplObj === undefined) {
      subExplObj = explObj.part.find(expl => expl.subset_type === "complement");
    }

    path.shift();

    return getExpl(subExplObj, path);
  }

}

export function initExplsTable(dbsObjs, subfsColumns) {

  let maxRow = dbsObjs.length;
  let maxCol = subfsColumns.length;

  let explsTable = new Array(maxRow).fill(null).map(() => Array(maxCol).fill(""));

  return explsTable;

}

export function exposeBoolTable(explObj, maxRow, maxCol, explsTable = []) {

  // Initialize empty matrix
  explsTable = (explsTable.length === 0) ? new Array(maxRow).fill(null).map(() => Array(maxCol).fill("")) : explsTable;

  // Expose boolean verdict in main subformula column
  let tblIndex = explObj.table.findIndex(tbl => tbl.col === 0);
  let tbl = explObj.table[tblIndex];
  explsTable[tbl.tp][tbl.col] = tbl.bool ? cellColor(true) : cellColor(false);

  // Expose (as a black cell) the boolean subproofs
  for (let i = 0; i < explObj.table.length; ++i) {
    let tbl = explObj.table[i];
    for (let j = 0; j < tbl.cells.length; ++j) {
      if (explsTable[tbl.cells[j].tp][tbl.cells[j].col] === "") {
        explsTable[tbl.cells[j].tp][tbl.cells[j].col] = black;
      }
    }
  }

  return explsTable;

}

export function updateBoolTable(explObj, explsTable) {

  return explsTable;
}

export function computeSquares(dbsObjs, explsObjs, squares = []) {

  // let maxRow = Math.max(explanations.length, atoms.length);
  // let maxCol = computeMaxCol(explanations) + 1;
  let maxRow = Math.max(dbsObjs.length);
  let maxCol = dbsObjs.nCols;

  // Initialize empty squares
  squares = (squares.length === 0) ? new Array(maxRow).fill(null).map(() => Array(maxCol).fill("")) : squares;

  // Populate cells with dbs
  // for (let tp = 0; tp < dbsObjs.length; ++tp) {
  //   if (dbsObjs[tp].dbs_row.length != 0) {
  //     let dbs = dbsObjs[tp].dbs;
  //     for (let j = 0; j < dbs[tp].length; ++j) {
  //       if (tp === dbs[j].tp) squares[tp][dbs[j].col] = dbs[j].db;
  //     }
  //   } else {
  //     for (let j = 0; j < maxCol; ++j) {
  //       if (tp === dbs[j].tp) squares[tp][dbs[j].col] = dbs[j].db;
  //     }
  //   }
  // }

  // Populate main subformula column with data
  // for (let tp = 0; tp < explanations.length; ++tp) {
  //   let tbl = explanations[tp].table;
  //   for (let j = 0; j < tbl.length; ++j) {
  //     if (tp === tbl[j].tp && tbl[j].col === atoms[0].aps.length) {
  //       squares[tp][tbl[j].col] = tbl[j].bool ? squareColor(true) : squareColor(false);
  //     }
  //   }
  // }

  // Initialize the other parts of the explanations with black
  // for (let i = 0; i < explanations.length; ++i) {
  //   for (let j = 0; j < explanations[i].table.length; ++j) {
  //     let tbl = explanations[i].table[j];
  //     for (let k = 0; k < tbl.cells.length; ++k) {
  //       squares[tbl.cells[k].tp][tbl.cells[k].col] = black;
  //     }
  //   }
  // }

  return squares;
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
