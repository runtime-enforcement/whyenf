import React, { useState } from 'react';
import Button from '@mui/material/Button';
import Menu from '@mui/material/Menu';
import DetailsIcon from '@mui/icons-material/Details';
import MenuInstance from './MenuInstance';
import { computeBooleanTable } from '../util';

function MainCell ({ expl, explsTable }) {

  // console.log(expl);

  // NestedMenuItem
  const [anchorEl, setAnchorEl] = useState(null);
  const open = Boolean(anchorEl);

  const handleFirstClick = (event) => setAnchorEl(event.currentTarget);
  const handleClose = () => setAnchorEl(null);
  const handleClick = (event) => {
    console.log(event);
    let path = [event.target.innerText];
  };

  if (expl.type === "leaf") {
    const explsTableUpdated = computeBooleanTable(expl.table, explsTable);
    return "";
  } else {
    if (expl.type === "node") {
      return (
        <div>
          <Button variant="contained" onClick={handleFirstClick}>
            <DetailsIcon />
          </Button>
          <Menu anchorEl={anchorEl} open={open} onClose={handleClose}>
            <MenuInstance expl={expl} open={open} handleClose={handleClose} handleClick={handleClick}/>
          </Menu>
        </div>
      );
    } else {
      return "";
    }
  }
}

export default MainCell;
