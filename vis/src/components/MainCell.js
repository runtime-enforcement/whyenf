import React, { useState } from 'react';
import Button from '@mui/material/Button';
import Menu from '@mui/material/Menu';
import DetailsIcon from '@mui/icons-material/Details';
import MenuInstance from './MenuInstance';

function MainCell ({ expl }) {

  // NestedMenuItem
  const [anchorEl, setAnchorEl] = useState(null);
  const open = Boolean(anchorEl);

  const handleClick = (event) => setAnchorEl(event.currentTarget);
  const handleClose = () => setAnchorEl(null);

  if (expl.type === "leaf") {
    return "";
  } else {
    if (expl.type === "node") {
      return (
        <div>
          <Button variant="contained" onClick={handleClick}>
            <DetailsIcon />
          </Button>
          <Menu anchorEl={anchorEl} open={open} onClose={handleClose}>
            <MenuInstance expl={expl} open={open} handleClose={handleClose}/>
          </Menu>
        </div>
      );
    } else {
      return "";
    }
  }
}

export default MainCell;
