import React, { useState } from 'react';
import { IconMenuItem } from 'mui-nested-menu';
import CancelIcon from '@mui/icons-material/Cancel';
import CheckCircleIcon from '@mui/icons-material/CheckCircle';
import Icon from '@mui/material/Icon';
import Box from '@mui/material/Box';
import { red, lightGreen, grey } from '@mui/material/colors';
import { getPolarity } from '../util';

function WrapperIconMenuItem ({ label, rightIcon, explObj, curCol, domainValues, variableNames, handleClick }) {

  const [menuSelected, setMenuSelected] = useState(false);

  const handleMouseEnter = () => {
    setMenuSelected(true);
  };

  const handleMouseLeave = () => {
    setMenuSelected(false);
  };

  const leftIcon =
        (getPolarity(explObj, curCol) === "true") ?
        <Box sx={{ maxHeight: 20 }}>
          <CheckCircleIcon fontSize="small" style={{ color: lightGreen[500] }}/>
          <Icon fontSize="small"/>
        </Box>
        : (getPolarity(explObj, curCol) === "false" ?
           <Box sx={{ maxHeight: 20 }}>
             <Icon fontSize="small"/>
             <CancelIcon fontSize="small" style={{ color: red[500] }}/>
           </Box>
           : (getPolarity(explObj, curCol) === "both" ?
              <Box sx={{ maxHeight: 20 }}>
                <CheckCircleIcon fontSize="small" style={{ color: lightGreen[500] }}/>
                <CancelIcon fontSize="small" style={{ color: red[500] }}/>
              </Box> : ""));

  return (
    <div onMouseEnter={handleMouseEnter}
         onMouseLeave={handleMouseLeave}>
      <IconMenuItem leftIcon={leftIcon}
                    rightIcon={rightIcon}
                    label={label}
                    style={ menuSelected ? {background: grey[200]} : {} }
                    onClick={(event) => { handleClick(event, domainValues, variableNames); }}>
      </IconMenuItem>
    </div>
  );
}

export default WrapperIconMenuItem;
