import React, { useState } from 'react';
import Button from '@mui/material/Button';
import Menu from '@mui/material/Menu';
import DetailsIcon from '@mui/icons-material/Details';
import MenuInstance from './MenuInstance';
import { collectValues, getCells, exposeColorsTable, updateCellsTable } from '../util';

function MainCell ({ explObj, colorsTable, cellsTable, setMonitorState }) {


  // NestedMenuItem
  const [anchorEl, setAnchorEl] = useState(null);
  const open = Boolean(anchorEl);

  const handleFirstClick = (event) => setAnchorEl(event.currentTarget);
  const handleClose = () => setAnchorEl(null);

  const handleClick = (event) => {

    let path = collectValues(event.target);
    path.push(event.target.innerText);
    let selCellsObj = getCells(explObj, path);

    let action = { type: "updateColorsAndCellsTable",
                   colorsTable: exposeColorsTable(selCellsObj, colorsTable.length, colorsTable[0].length, colorsTable),
                   cellsTable: updateCellsTable(selCellsObj, cellsTable)
                 };
    setMonitorState(action);
  };


  if (explObj.type === "leaf") {
    return "";
  } else {
    if (explObj.type === "node") {
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
