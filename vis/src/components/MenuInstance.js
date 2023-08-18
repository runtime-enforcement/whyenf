import React, { useState } from 'react';
import ArrowRightIcon from '@mui/icons-material/ArrowRight';
import MenuItem from '@mui/material/MenuItem';
import WrapperNestedMenuItem from './WrapperNestedMenuItem';
import WrapperIconMenuItem from './WrapperIconMenuItem';

function MenuInstance ({ explObj, open, curCol, handleClose, handleClick }) {

  // undefined checks: quantifiers related
  if (explObj.type === "node" || explObj.kind === "partition") {
    return (
      <div>
        <MenuItem disabled={true}>
          {explObj.var}
        </MenuItem>
        { explObj?.part?.map((el, i) => {
          const ds = el.subset_type === "finite" ?
                el.subset_values.join(', ') : (<span style={{fontWeight: 'bold'}}>Other</span>);
          if (el.type === "node" || el.kind === "partition") {
            return (
              <div key={i}>
                <WrapperNestedMenuItem rightIcon={<ArrowRightIcon/>}
                                       label={ds}
                                       explObj={el}
                                       curCol={curCol}
                                       parentMenuOpen={open}>
                  <div data-value={ds}>
                    <MenuInstance explObj={el}
                                  open={open}
                                  curCol={curCol}
                                  handleClose={handleClose}
                                  handleClick={handleClick}/>
                  </div>
                </WrapperNestedMenuItem>
              </div>
            );
          } else {
            return (
              <div key={i}>
                <WrapperIconMenuItem label={ds}
                                     explObj={el}
                                     curCol={curCol}
                                     handleClick={handleClick}/>
              </div>
            );
          }
        })}
      </div>
    );
  } else {
    return "";
  }
}

export default MenuInstance;
