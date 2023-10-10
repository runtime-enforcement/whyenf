import React from 'react';
import Typography from '@mui/material/Typography';
import Box from '@mui/material/Box';
import ArrowRightIcon from '@mui/icons-material/ArrowRight';
import MenuItem from '@mui/material/MenuItem';
import WrapperNestedMenuItem from './WrapperNestedMenuItem';
import WrapperIconMenuItem from './WrapperIconMenuItem';

function MenuInstance ({ explObj, curCol, open, domainValues, variableNames, handleClose, handleClick }) {

  if (explObj.type === "node" || explObj.kind === "partition") {
    const newVariableNames = [];

    newVariableNames.push(...variableNames);
    newVariableNames.push(explObj.var);

    return (
      <div>
        <Box sx={{ ml: 1, mr: 1, mb: 1, borderRadius: '9px' }}
             style={{ color: "#FFFFFF",
                      opacity: 1.0,
                      background: "#000000" }}>
          <MenuItem disabled={true}
                    sx={{ justifyContent: 'center' }}
                    style={{ opacity: 1.0 }}>
            <Typography variant="h6">{explObj.var}</Typography>
          </MenuItem>
        </Box>
        { explObj?.part?.map((el, i) => {

          let domainValueLabel;

          if (el.subset_type === "finite") {

            let fullString = el.subset_values.join(', ');

            if (fullString.length > 27) {
              let commaPosition = fullString.search(",");
              if (commaPosition < 12) {
                let commaPositionEnd = fullString.split("").reduce((acc, c) => c + acc, "").search(",");
                domainValueLabel = fullString.slice(0,commaPosition) + ', ..., ' +
                  fullString.slice(fullString.length-commaPositionEnd,fullString.length);
              } else {
                domainValueLabel = fullString.slice(0,12) + '...' +
                  fullString.slice(fullString.length-12,fullString.length);
              }
            } else {
              domainValueLabel = fullString;
            }

          } else {
            if (i === 0) {
              domainValueLabel = (<span style={{fontWeight: 'bold'}}>Any</span>);
            } else {
              domainValueLabel = (<span style={{fontWeight: 'bold'}}>Other</span>);
            }
          }

          let domainValueTable = el.subset_type === "finite" ?
              el.subset_values.join(', ') : "𝔻 ∖ ".concat(el.subset_values.join(', '));
          if (el.subset_values.length === 0) domainValueTable = "𝔻";

          const newDomainValues = [];
          newDomainValues.push(...domainValues);
          newDomainValues.push(domainValueTable);

          if (el.type === "node" || el.kind === "partition") {
            return (
              <div key={i}>
                <WrapperNestedMenuItem rightIcon={<ArrowRightIcon/>}
                                       label={domainValueLabel}
                                       explObj={el}
                                       curCol={curCol}
                                       parentMenuOpen={open}>
                  <MenuInstance explObj={el}
                                curCol={curCol}
                                open={open}
                                domainValues={newDomainValues}
                                variableNames={newVariableNames}
                                handleClose={handleClose}
                                handleClick={handleClick}/>
                </WrapperNestedMenuItem>
              </div>
            );
          } else {
            return (
              <div key={i}>
                <WrapperIconMenuItem label={domainValueLabel}
                                     explObj={el}
                                     curCol={curCol}
                                     domainValues={newDomainValues}
                                     variableNames={newVariableNames}
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
