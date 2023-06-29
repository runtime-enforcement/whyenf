import React from 'react';
import ArrowRightIcon from '@mui/icons-material/ArrowRight';
import MenuItem from '@mui/material/MenuItem';
import { NestedMenuItem } from 'mui-nested-menu';

function MenuInstance ({ explObj, open, handleClose, handleClick }) {

  // undefined checks: quantifiers related
  if (explObj.type === "node" || explObj.kind === "partition") {
    return (
      <div>
        <MenuItem disabled={true}>{explObj.var}</MenuItem>
        { explObj?.part?.map((el, i) => {
          const ds = el.subset_type === "finite" ?
                el.subset_values.join(', ') : (<span style={{fontWeight: 'bold'}}>Other</span>);
          if (el.type === "node" || el.kind === "partition") {
            return (
              <div key={i}>
                <NestedMenuItem rightIcon={<ArrowRightIcon/>}
                                label={ds}
                                parentMenuOpen={open}>
                  <div data-value={ds}>
                    <MenuInstance explObj={el} open={open} handleClose={handleClose} handleClick={handleClick}/>
                  </div>
                </NestedMenuItem>
              </div>
            );
          } else {
            return (
              <div key={i}>
                <MenuItem onClick={handleClick}>{ds}</MenuItem>
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
