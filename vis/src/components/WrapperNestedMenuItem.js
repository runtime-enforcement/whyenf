import React, { useState } from 'react';
import { NestedMenuItem } from 'mui-nested-menu';
import CancelIcon from '@mui/icons-material/Cancel';
import CheckCircleIcon from '@mui/icons-material/CheckCircle';
import Icon from '@mui/material/Icon';
import { red, lightGreen } from '@mui/material/colors';
import Box from '@mui/material/Box';
import { getPolarity } from '../util';

function WrapperNestedMenuItem ({ label, rightIcon, explObj, curCol, parentMenuOpen, children }) {

  const [menuSelected, setMenuSelected] = useState(false);

  const handleMouseEnter = (event) => {
    setMenuSelected(true);
  };

  const handleMouseLeave = () => {
    setMenuSelected(false);
  };

  const leftIcon =
        (getPolarity(explObj, curCol) === "true") ?
        <Box>
          <CheckCircleIcon fontSize="small" style={{ color: lightGreen[500] }}/>
          <Icon fontSize="small"/>
        </Box>
        : (getPolarity(explObj, curCol) === "false" ?
           <Box>
             <Icon fontSize="small"/>
             <CancelIcon fontSize="small" style={{ color: red[500] }}/>
           </Box>
           : (getPolarity(explObj, curCol) === "both" ?
              <Box>
                <CheckCircleIcon fontSize="small" style={{ color: lightGreen[500] }}/>
                <CancelIcon fontSize="small" style={{ color: red[500] }}/>
              </Box> : ""));

  return (
    <div onMouseEnter={handleMouseEnter}
         onMouseLeave={handleMouseLeave}>

      <NestedMenuItem leftIcon={leftIcon}
                      rightIcon={rightIcon}
                      label={label}
                      parentMenuOpen={parentMenuOpen}
                      style={menuSelected ? {background: "#fdd835"} : {}}>
        {children}
      </NestedMenuItem>
    </div>
  );
}

export default WrapperNestedMenuItem;
