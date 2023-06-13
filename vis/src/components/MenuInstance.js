import React, { useState } from 'react';
import ArrowRightIcon from '@mui/icons-material/ArrowRight';
import MenuItem from '@mui/material/MenuItem';
import { IconMenuItem, NestedMenuItem } from 'mui-nested-menu';

function MenuInstance ({ expl, open, handleClose }) {

  if (expl.type === "node") {
    return (
      <div>
        <MenuItem disabled={true}>{expl.var}</MenuItem>
        { expl?.part?.map((el, i) => {
          const ds = el.subset_type === "finite" ?
                el.subset_values.join(', ') : '*';
          if (el.type === "node") {
            return (
              <div key={i}>
                <NestedMenuItem rightIcon={<ArrowRightIcon/>}
                                label={ds}
                                parentMenuOpen={open}>
                  <MenuInstance expl={el} open={open} handleClose={handleClose}/>
                </NestedMenuItem>
              </div>
            );
          } else {
            return (
              <div key={i}>
                <MenuItem onClick={handleClose}>{ds}</MenuItem>
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
