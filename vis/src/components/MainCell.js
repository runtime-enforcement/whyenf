import React, { useState } from 'react';
import Button from '@mui/material/Button';
import Menu from '@mui/material/Menu';
import DetailsIcon from '@mui/icons-material/Details';
import MenuInstance from './MenuInstance';
import { collectValues, getExpl, exposeBoolTable, updateBoolTable } from '../util';

function MainCell ({ explObj, explsTable, setMonitorState }) {


  // NestedMenuItem
  const [anchorEl, setAnchorEl] = useState(null);
  const open = Boolean(anchorEl);

  const handleFirstClick = (event) => setAnchorEl(event.currentTarget);
  const handleClose = () => setAnchorEl(null);

  const handleClick = (event) => {
    let path = collectValues(event.target);
    path.push(event.target.innerText);

    let selExplObj = getExpl(explObj, path);

    let action = { type: "updateExplsTable",
                   explsTable: exposeBoolTable(selExplObj, explsTable.length, explsTable[0].length, explsTable),
                 };
    setMonitorState(action);
  };


  if (explObj.type === "leaf") {
    const explsTableUpdated = updateBoolTable(explObj.table, explsTable);
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
