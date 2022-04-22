import Button from '@mui/material/Button';
import { red, purple, yellow, lightGreen } from '@mui/material/colors';

function computeMaxCol(explanations) {
  let maxCol = 0;

  for (let tp = 0; tp < explanations.length; ++tp) {
    let tbl = explanations[tp].table;
    for (let j = 0; j < tbl.length; ++j) {
      if (tbl[j].col > maxCol) maxCol = tbl[j].col;
    }
  }

  return maxCol;
}

export function squareColor(bool) {
  return (bool ? lightGreen[500] : red[500]);
}

export function squareColorTest(bool) {
  return (bool ? yellow[500] : purple[500]);
}

export function computeSquares(explanations, atoms, squares = []) {

  let maxRow = atoms.length;
  let maxCol = computeMaxCol(explanations);

  // Initialize empty squares
  squares = (squares.length === 0) ? new Array(maxRow).fill(null).map(() => Array(maxCol+3).fill("")) : squares;

  // Populate atoms with data
  for (let tp = 0; tp < atoms.length; ++tp) {
    let aps = atoms[tp].aps;
    for (let j = 0; j < aps.length; ++j) {
      if (tp === aps[j].tp) {
        squares[tp][aps[j].col] = aps[j].bool ? squareColor(true) : squareColor(false);
      }
    }
  }

  // Populate main subformula column with data
  for (let tp = 0; tp < explanations.length; ++tp) {
    let tbl = explanations[tp].table;
    for (let j = 0; j < tbl.length; ++j) {
      if (tp === tbl[j].tp && tbl[j].col === atoms[0].aps.length) {
        squares[tp][tbl[j].col] = tbl[j].bool ? squareColor(true) : squareColor(false);
      }
    }
  }

  return squares;
}

export function tpsIn(ts, tp, interval, period, atoms) {
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
    b = parseInt(bString);
    l = ts + a;
    r = ts + b;
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

  let translatedError = {};

  if (error.message === undefined && error[1].c !== undefined) {
    switch (error[1].c) {
    case "Lib.Mtl_parser.MenhirBasics.Error":
      translatedError = { name: "Error",
                          message: "Formula could not be parsed.\n\nPlease make sure the syntax is correct."
                        };
      break;
    case "Lib.Monitor.UNBOUNDED_FUTURE":
      translatedError = { name: "Error",
                          message: "Your formula has an unbounded UNTIL.\n\nPlease make sure all UNTIL instances are bounded."
                        };
    }
  } else {
    if (error.message.includes("Unexpected token")) {
      translatedError = { name: "Error",
                          message: "Trace could not be parsed.\n\nPlease make sure the syntax is correct."
                        };
    }
  }

  return translatedError;
}
