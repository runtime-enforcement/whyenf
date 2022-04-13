import Filter1Icon from '@mui/icons-material/Filter1';
import Filter2Icon from '@mui/icons-material/Filter2';
import Filter3Icon from '@mui/icons-material/Filter3';
import Filter4Icon from '@mui/icons-material/Filter4';
import Filter5Icon from '@mui/icons-material/Filter5';
import Filter6Icon from '@mui/icons-material/Filter6';
import Filter7Icon from '@mui/icons-material/Filter7';
import Filter8Icon from '@mui/icons-material/Filter8';
import Filter9Icon from '@mui/icons-material/Filter9';
import CropSquareIcon from '@mui/icons-material/CropSquare';
import Button from '@mui/material/Button';
import { red, purple, yellow, lightGreen } from '@mui/material/colors';

export function pickColumnItem(i, f) {
  switch (i) {
  case 0:
    return (
      <Button
        onClick={() => {
          alert();
        }}
      >
        <Filter1Icon />
      </Button>
    );
  case 1:
    return <Filter2Icon />;
  case 2:
    return <Filter3Icon />;
  case 3:
    return <Filter4Icon />;
  case 4:
    return <Filter5Icon />;
  case 5:
    return <Filter6Icon />;
  case 6:
    return <Filter7Icon />;
  case 7:
    return <Filter8Icon />;
  case 8:
    return <Filter9Icon />;
  default:
    return <CropSquareIcon />;
  }
}

export function squareColor(bool) {
  return (bool ? lightGreen[500] : red[500]);
}

export function squareColorTest(bool) {
  return (bool ? yellow[500] : purple[500]);
}

export function initSquares(explanations, atoms) {

  let maxRow = explanations.length;
  let maxCol = 0;

  // Find maxCol
  for (let tp = 0; tp < explanations.length; ++tp) {
    let tbl = explanations[tp].table;
    for (let j = 0; j < tbl.length; ++j) {
      if (tbl[j].col > maxCol) maxCol = tbl[j].col;
    }
  }

  // Initialize empty squares
  var squares = new Array(maxRow).fill(null).map(() => Array(maxCol+3).fill(""));

  // Populate atoms with data
  for (let tp = 0; tp < atoms.length; ++tp) {
    let aps = atoms[tp].aps;
    for (let j = 0; j < aps.length; ++j) {
      if (tp === aps[j].tp) {
        switch(aps[j].bool) {
        case true:
          squares[tp][aps[j].col] = squareColor(true);
          break;
        case false:
          squares[tp][aps[j].col] = squareColor(false);
          break;
        }
      }
    }
  }

  // Populate main subformula column with data
  for (let tp = 0; tp < explanations.length; ++tp) {
    let tbl = explanations[tp].table;
    for (let j = 0; j < tbl.length; ++j) {
      if (tp === tbl[j].tp && tbl[j].col === atoms[0].aps.length) {
        switch(tbl[j].bool) {
        case true:
          squares[tp][tbl[j].col] = squareColor(true);
          break;
        case false:
          squares[tp][tbl[j].col] = squareColor(false);
          break;
        }
      }
    }
  }

  return squares;
}

export function tpsIn (ts, tp, interval, period, explanations) {
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

  for (let i = 0; i < explanations.length; ++i) {
    if (explanations[i].ts >= l && explanations[i].ts <= r
        && ((period === "past" && explanations[i].tp <= tp)
            || (period === "future" && explanations[i].tp >= tp))) {
      idxs.push(i);
    }
  }

  return idxs;
}

export function translateError (error) {
  console.log(error);

  let translatedError = {};

  if (error.message === undefined && error[1].c !== undefined) {
    switch (error[1].c) {
    case "Lib.Mtl_parser.MenhirBasics.Error":
      translatedError = { name: "Error",
                          message: "Formula could not be parsed.\n\nPlease make sure the syntax is correct."
                        }
      break;
    case "Lib.Monitor.UNBOUNDED_FUTURE":
      translatedError = { name: "Error",
                          message: "Your formula has an unbounded UNTIL.\n\nPlease make sure all UNTIL instances are bounded." }
    }
  } else {
    if (error.message.includes("Unexpected token")) {
      translatedError = { name: "Error", message: "Trace could not be parsed.\n\nPlease make sure the syntax is correct." }
    }
  }

  return translatedError;
}
