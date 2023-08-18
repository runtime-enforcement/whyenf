import React, { useState } from 'react';
import Button from '@mui/material/Button';
import IconButton from '@mui/material/IconButton';
import Menu from '@mui/material/Menu';
import CancelIcon from '@mui/icons-material/Cancel';
import CheckCircleIcon from '@mui/icons-material/CheckCircle';
import Icon from '@mui/material/Icon';
import KeyboardArrowDownIcon from '@mui/icons-material/KeyboardArrowDown';
import DataObjectIcon from '@mui/icons-material/DataObject';
import MenuInstance from './MenuInstance';
import { red, lightGreen } from '@mui/material/colors';
import { collectValues,
         getCells,
         exposeColorsTableMain,
         exposeColorsTableQuant,
         updateCellsTableMain,
         updateCellsTableQuant,
         getPolarity } from '../util';

function MenuCell ({ explObj, colorsTable, cellsTable, curCol, setMonitorState }) {

  // NestedMenuItem
  const [anchorEl, setAnchorEl] = useState(null);
  const open = Boolean(anchorEl);

  const handleFirstClick = (event) => setAnchorEl(event.currentTarget);
  const handleClose = () => setAnchorEl(null);

  const handleClick = (event) => {

    if (explObj.type === "node") {

      let path = collectValues(event.target);
      path.push(event.target.innerText);
      let selCellsObj = getCells(explObj, path);

      let action = { type: "updateColorsAndCellsTable",
                     colorsTable: exposeColorsTableMain(selCellsObj,
                                                        colorsTable.length,
                                                        colorsTable[0].length),
                     cellsTable: updateCellsTableMain(selCellsObj, cellsTable)
                   };
      setMonitorState(action);

    } else {
      if (explObj.type === "leaf") {
        let action = { type: "updateColorsAndCellsTable",
                       colorsTable: exposeColorsTableMain(explObj,
                                                          colorsTable.length,
                                                          colorsTable[0].length),
                       cellsTable: updateCellsTableMain(explObj, cellsTable)
                   };
        setMonitorState(action);
      } else {
        if (explObj.kind === "partition") {
          let selCellsObj = getCells(explObj, [event.target.innerText]);
          // console.log(selCellsObj);
          let action = { type: "updateColorsAndCellsTable",
                         colorsTable: exposeColorsTableQuant(selCellsObj, curCol + 1, colorsTable),
                         cellsTable: updateCellsTableQuant(selCellsObj, curCol, cellsTable)
                       };
          setMonitorState(action);
        }
      }
    }

    setAnchorEl(null);

  };

  if (explObj.type === "leaf") {
    return <IconButton onClick={handleClick}>
             <DataObjectIcon fontSize="small"/>
           </IconButton>;
  } else {
    if (explObj.type === "node" || explObj.kind === "partition") {
      return (
        <div>
          { getPolarity(explObj, curCol) === "true" ?
            <Button variant="text"
                    style={{ minWidth: "80px" }}
                    onClick={handleFirstClick}
            >
              <CheckCircleIcon fontSize="small" style={{ color: lightGreen[500] }}/>
              <Icon fontSize="small"/>
              <KeyboardArrowDownIcon fontSize="small" />
            </Button> : "" }

          { getPolarity(explObj, curCol) === "false" ?
            <Button variant="text"
                    style={{ minWidth: "80px" }}
                    onClick={handleFirstClick}
            >
              <Icon fontSize="small"/>
              <CancelIcon fontSize="small" style={{ color: red[500] }}/>
              <KeyboardArrowDownIcon fontSize="small" />
            </Button>
            : "" }

          { getPolarity(explObj, curCol) === "both" ?
            <Button variant="text"
                    style={{ minWidth: "80px" }}
                    onClick={handleFirstClick}
            >
              <CheckCircleIcon fontSize="small" style={{ color: lightGreen[500] }}/>
              <CancelIcon fontSize="small" style={{ color: red[500] }}/>
              <KeyboardArrowDownIcon fontSize="small" />
            </Button> : "" }
          <Menu anchorEl={anchorEl} open={open} onClose={handleClose}>
            <MenuInstance explObj={explObj} open={open} curCol={curCol} handleClose={handleClose} handleClick={handleClick}/>
          </Menu>
        </div>
      );
    } else {
      return "";
    }
  }
}

export default MenuCell;
