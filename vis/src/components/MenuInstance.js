import React, { useState } from 'react';
import ArrowRightIcon from '@mui/icons-material/ArrowRight';
import MenuItem from '@mui/material/MenuItem';
import WrapperNestedMenuItem from './WrapperNestedMenuItem';
import WrapperIconMenuItem from './WrapperIconMenuItem';

function MenuInstance ({ explObj, curCol, open, domainValues, handleClose, handleClick }) {

  if (explObj.type === "node" || explObj.kind === "partition") {
    return (
      <div>
        <MenuItem disabled={true}
                  sx={{ justifyContent: 'center' }}
                  style={{ color: "#FFFFFF",
                           opacity: 1.0,
                           background: "#000000"}}>
          <span>
            {explObj.var}
          </span>
        </MenuItem>
        { explObj?.part?.map((el, i) => {

          const domainValue = el.subset_type === "finite" ?
                el.subset_values.join(', ') : (<span style={{fontWeight: 'bold'}}>Other</span>);
          const newDomainValues = [];
          newDomainValues.push(...domainValues);
          newDomainValues.push(domainValue);

          if (el.type === "node" || el.kind === "partition") {
            return (
              <div key={i}>
                <WrapperNestedMenuItem rightIcon={<ArrowRightIcon/>}
                                       label={domainValue}
                                       explObj={el}
                                       curCol={curCol}
                                       parentMenuOpen={open}>
                  <MenuInstance explObj={el}
                                curCol={curCol}
                                open={open}
                                domainValues={newDomainValues}
                                handleClose={handleClose}
                                handleClick={handleClick}/>
                </WrapperNestedMenuItem>
              </div>
            );
          } else {
            return (
              <div key={i}>
                <WrapperIconMenuItem label={domainValue}
                                     explObj={el}
                                     curCol={curCol}
                                     domainValues={newDomainValues}
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
