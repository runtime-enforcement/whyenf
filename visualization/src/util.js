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
import { red, lightGreen } from '@mui/material/colors';

// function convertToMTL(explanation) {
//   switch (explanation.type) {
//   case "STT":
//     return { type: "TT" };
//   case "SAtom":
//     return { type: "P", atom: explanation.atom };
//   case "SNeg":
//     return { type: "Neg", formula: convertToMTL(explanation.explanation) };
//   case "SDisjL":
//     return { type: "Disj", lformula: convertToMTL(explanation.explanation) };
//   case "SDisjR":
//     return { type: "Disj", rformula: convertToMTL(explanation.explanation) };
//   case "SConj":
//     return { type: "Conj",
//              lformula: convertToMTL(explanation.lexplanation),
//              rformula: convertToMTL(explanation.rexplanation) };
//   case "SPrev":
//     return {type: "Prev", formula: convertToMTL(explanation.explanation)};
//   case "SNext":
//     return {type: "Next", formula: convertToMTL(explanation.explanation)};
//   case "SSince":
//     return { type: "Since",
//              lformula: convertToMTL(explanation.explanation),
//              rformula: convertToMTL(explanation.explanations['0explanation']) };
//   case "SUntil":
//     return { type: "Until",
//              lformula: convertToMTL(explanation.explanation),
//              rformula: convertToMTL(explanation.explanations['0explanation']) };
//   case "VFF":
//     return { type: "FF" };
//   case "VAtom":
//     return { type: "P", atom: explanation.atom };
//   case "VNeg":
//     return {type: "Neg", formula: convertToMTL(explanation.explanation)};
//   case "VDisj":
//     return { type: "Disj",
//              lformula: convertToMTL(explanation.lexplanation),
//              rformula: convertToMTL(explanation.rexplanation) };
//   case "VConjL":
//     return { type: "Conj", lformula: convertToMTL(explanation.explanation) };
//   case "VConjR":
//     return { type: "Conj", rformula: convertToMTL(explanation.explanation) };
//   case "VPrev":
//     return { type: "Prev", formula: convertToMTL(explanation.explanation) };
//   case "VNext":
//     return { type: "Next", formula: convertToMTL(explanation.explanation) };
//   case "VSince":
//     return { type: "Since",
//              lformula: convertToMTL(explanation.explanation),
//              rformula: convertToMTL(explanation.explanations['0explanation']) };
//   case "VSinceInf":
//     return { type: "Since",
//              rformula: convertToMTL(explanation.explanations['0explanation']) };
//   case "VUntil":
//     return { type: "Until",
//              lformula: convertToMTL(explanation.explanation),
//              rformula: convertToMTL(explanation.explanations['0explanation']) };
//   case "VUntilInf":
//     return { type: "Until",
//              rformula: convertToMTL(explanation.explanations['0explanation']) };
//   }
// }

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

export function squareColor(explanationType) {
  return (explanationType.charAt(0) === 'S' ? lightGreen[500] : red[500]);
}

function match(explanation, f) {
  switch (explanation.type) {
  case "STT":
    return f.type === "TT";
  case "SAtom":
    return f.atom === explanation.atom;
  case "SNeg":
    return (f.type === "Neg") ? match(explanation.explanation, f.formula) : false;
  case "SDisjL":
    return (f.type === "Disj") ? match(explanation.explanation, f.lformula) : false;
  case "SDisjR":
    return (f.type === "Disj") ? match(explanation.explanation, f.rformula) : false;
  case "SConj":
    return (f.type === "Conj") ? (match(explanation.lexplanation, f.lformula) && match(explanation.rexplanation, f.rformula)) : false;
  case "SPrev":
    return (f.type === "Prev") ? match(explanation.explanation, f.formula) : false;
  case "SNext":
    return (f.type === "Next") ? match(explanation.explanation, f.formula) : false;
  case "SSince":
    return (f.type === "Since") ? (match(explanation.explanation, f.lformula) && match(explanation.explanations['0explanation'], f.rformula)) : false;
  case "SUntil":
    return (f.type === "Until") ? (match(explanation.explanation, f.lformula) && match(explanation.explanations['0explanation'], f.rformula)) : false;
  case "VFF":
    return f.type === "FF";
  case "VAtom":
    return f.atom === explanation.atom;
  case "VNeg":
    return (f.type === "Neg") ? match(explanation.explanation, f.formula) : false;
  case "VDisj":
    return (f.type === "Disj") ? (match(explanation.lexplanation, f.lformula) && match(explanation.rexplanation, f.rformula)) : false;
  case "VConjL":
    return (f.type === "Conj") ? match(explanation.explanation, f.lformula) : false;
  case "VConjR":
    return (f.type === "Conj") ? match(explanation.explanation, f.rformula) : false;
  case "VPrev":
    return (f.type === "Prev") ? match(explanation.explanation, f.formula) : false;
  case "VNext":
    return (f.type === "Next") ? match(explanation.explanation, f.formula) : false;
  case "VSince":
    return (f.type === "Since") ? (match(explanation.explanation, f.lformula) && match(explanation.explanations['0explanation'], f.rformula)) : false;
  case "VSinceInf":
    return (f.type === "Since") ? match(explanation.explanations['0explanation'], f.rformula) : false;
  case "VUntil":
    return (f.type === "Until") ? (match(explanation.explanation, f.lformula) && match(explanation.explanations['0explanation'], f.rformula)) : false;
  case "VUntilInf":
    return (f.type === "Until") ? match(explanation.explanations['0explanation'], f.rformula) : false;
  default:
    return false;
  }
}

function findMatch(explanation, subformulas) {
  for (let i = 0; i < subformulas.length; ++i) {
    if (match(explanation, subformulas[i].formula)) return i;
  }
}

export function changedSquares(explanation, subformulas) {
  var chSquares = [];

  switch (explanation.type) {
  case "STT":
  case "SAtom":
  case "VFF":
  case "VAtom":
    chSquares.push({ tp: explanation.tp,
                          col: findMatch(explanation, subformulas),
                          color: squareColor(explanation.type) });
    break;
  case "SNeg":
  case "SDisjL":
  case "SDisjR":
  case "SPrev":
  case "SNext":
  case "VNeg":
  case "VConjL":
  case "VConjR":
  case "VPrev":
  case "VNext":
    chSquares.push({ tp: explanation.explanation.tp,
                          col: findMatch(explanation.explanation, subformulas),
                          color: squareColor(explanation.explanation.type) });
    break;
  case "SConj":
  case "VDisj":
    chSquares.push({ tp: explanation.lexplanation.tp,
                          col: findMatch(explanation.lexplanation, subformulas),
                          color: squareColor(explanation.lexplanation.type) });
    chSquares.push({ tp: explanation.rexplanation.tp,
                          col: findMatch(explanation.rexplanation, subformulas),
                          color: squareColor(explanation.rexplanation.type) });
    break;
  case "SSince":
  case "SUntil":
  case "VSince":
  case "VUntil":
    chSquares.push({ tp: explanation.explanation.tp,
                          col: findMatch(explanation.explanation, subformulas),
                          color: squareColor(explanation.explanation.type) });
    if (!(Object.keys(explanation.explanations).length === 0)) {
      chSquares.push({ tp: explanation.explanations['0explanation'].tp,
                            col: findMatch(explanation.explanations['0explanation'], subformulas),
                            color: squareColor(explanation.explanations['0explanation'].type) });
    }
    break;
  case "VSinceInf":
  case "VUntilInf":
    if (!(Object.keys(explanation.explanations).length === 0)) {
      chSquares.push({ tp: explanation.explanations['0explanation'].tp,
                            col: findMatch(explanation.explanations['0explanation'], subformulas),
                            color: squareColor(explanation.explanations['0explanation'].type) });
    }
    break;
  default:
    break;
  }

  return chSquares;
}
