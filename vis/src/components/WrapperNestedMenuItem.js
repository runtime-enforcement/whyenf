import React, { useState } from 'react';
import { NestedMenuItem } from 'mui-nested-menu';

function WrapperNestedMenuItem ({ label, rightIcon, parentMenuOpen, children }) {

  const [menuSelected, setMenuSelected] = useState(false);

  const handleMouseEnter = () => {
    setMenuSelected(true);
  };

  const handleMouseLeave = () => {
    setMenuSelected(false);
  };

  return (
    <div onMouseEnter={handleMouseEnter}
         onMouseLeave={handleMouseLeave}>
      <NestedMenuItem rightIcon={rightIcon}
                      label={label}
                      parentMenuOpen={parentMenuOpen}
                      style={ menuSelected ? {background: "#fdd835"} : {}}>
        {children}
      </NestedMenuItem>
    </div>
  );
}

export default WrapperNestedMenuItem;
