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

  var squares = [];

  for (let tp = 0; tp < explanations.length; ++tp) {
    let tbl = explanations[tp].table;
    squares[tp] = [];
    // console.log(tbl);
    for (let j = 0; j < tbl.length; ++j) {
      if (tp === tbl[j].tp && tbl[j].col === 0) {
        switch(tbl[j].bool) {
        case true:
          squares[tp][tbl[j].col] = squareColor(true);
          break;
        case false:
          squares[tp][tbl[j].col] = squareColor(false);
          break;
        default:
          squares[tp][tbl[j].col] = "primary";
          break;
        }
      }
    }
  }

  for (let tp = 0; tp < atoms.length; ++tp) {
    let aps = atoms[tp].aps;
    console.log(aps);
    for (let j = 0; j < aps.length; ++j) {
      if (tp === aps[j].tp) {
        switch(aps[j].bool) {
        case true:
          squares[tp][aps[j].col] = squareColor(true);
          break;
        case false:
          squares[tp][aps[j].col] = squareColor(false);
          break;
        default:
          squares[tp][aps[j].col] = "primary";
          break;
        }
      }
    }
  }

  return squares;
}