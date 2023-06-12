import React, { useState } from 'react';
import Button from '@mui/material/Button';
import DetailsIcon from '@mui/icons-material/Details';
import ArrowRightIcon from '@mui/icons-material/ArrowRight';
import MenuItem from '@mui/material/MenuItem';
import Menu from '@mui/material/Menu';
import { IconMenuItem, NestedMenuItem } from 'mui-nested-menu';


function MainCell ({ explsObjs }) {

  // NestedMenuItem
  const [anchorEl, setAnchorEl] = useState(null);
  const open = Boolean(anchorEl);

  const handleClick = (event) => setAnchorEl(event.currentTarget);
  const handleClose = () => setAnchorEl(null);

  return (
    <div>
      <Button
        variant="contained"
        onClick={handleClick}
      >
        <DetailsIcon />
      </Button>
      <Menu anchorEl={anchorEl} open={open} onClose={handleClose}>
        <NestedMenuItem
          rightIcon={<ArrowRightIcon/>}
          label="Top Level"
          parentMenuOpen={open}
        >
          <MenuItem onClick={handleClose}>Standard Menu Item!</MenuItem>
          <IconMenuItem
            onClick={handleClose}
            label="Icon Menu Item"
          />
          <NestedMenuItem
            rightIcon={<ArrowRightIcon />}
            label="Go deeper!"
            parentMenuOpen={open}
          >
            <MenuItem onClick={handleClose}>Standard Menu Item!</MenuItem>
            <IconMenuItem
              onClick={handleClose}
              label="Icon Menu Item"
            />
          </NestedMenuItem>
        </NestedMenuItem>
      </Menu>
    </div>
  );
}

export default MainCell;
