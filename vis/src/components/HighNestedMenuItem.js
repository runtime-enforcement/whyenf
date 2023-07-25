import React, { useState } from 'react';
import { NestedMenuItem } from 'mui-nested-menu';

function HighNestedMenuItem ({ label, rightIcon, parentMenuOpen, children }) {

  console.log(parentMenuOpen);

  return (
    <NestedMenuItem rightIcon={rightIcon}
                    label={label}
                    parentMenuOpen={parentMenuOpen}
                    className="open-menu">
      {children}
    </NestedMenuItem>
  );
}

export default HighNestedMenuItem;
