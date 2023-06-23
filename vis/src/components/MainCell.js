import React, { useState } from 'react';
import Button from '@mui/material/Button';
import Menu from '@mui/material/Menu';
import DetailsIcon from '@mui/icons-material/Details';
import MenuInstance from './MenuInstance';
import { collectValues,
         getCells,
         exposeColorsTableMain,
         exposeColorsTableQuant,
         updateCellsTableMain,
         updateCellsTableQuant } from '../util';

function MainCell ({ explObj, colorsTable, cellsTable, nextCol, tp, setMonitorState }) {

  // NestedMenuItem
  const [anchorEl, setAnchorEl] = useState(null);
  const open = Boolean(anchorEl);

  const handleFirstClick = (event) => setAnchorEl(event.currentTarget);
  const handleClose = () => setAnchorEl(null);

  const handleClick = (event) => {

    if (explObj.type === "leaf" || explObj.type === "node") {

      let path = collectValues(event.target);
      path.push(event.target.innerText);
      let selCellsObj = getCells(explObj, path);

      let action = { type: "updateColorsAndCellsTable",
                     colorsTable: exposeColorsTableMain(selCellsObj, colorsTable.length, colorsTable[0].length),
                     cellsTable: updateCellsTableMain(selCellsObj, cellsTable)
                   };
      setMonitorState(action);

    } else {

      if (explObj.kind === "partition") {
        let curCol = nextCol - 1;
        let selCellsObj = getCells(explObj, [event.target.innerText]);
        let action = { type: "updateColorsAndCellsTable",
                       colorsTable: exposeColorsTableQuant(selCellsObj, nextCol, colorsTable),
                       cellsTable: updateCellsTableQuant(selCellsObj, tp, curCol, cellsTable)
                     };
        setMonitorState(action);
      }
    }

  };


  if (explObj.type === "leaf") {
    return "";
  } else {
    if (explObj.type === "node" || explObj.kind === "partition") {
      return (
        <div>
          <Button variant="contained" onClick={handleFirstClick}>
            <DetailsIcon />
          </Button>
          <Menu anchorEl={anchorEl} open={open} onClose={handleClose}>
            <MenuInstance explObj={explObj} open={open} handleClose={handleClose} handleClick={handleClick}/>
          </Menu>
        </div>
      );
    } else {
      return "";
    }
  }
}

export default MainCell;
