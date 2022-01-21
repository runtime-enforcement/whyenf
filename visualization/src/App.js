import React from 'react';
import logo from './logo.svg';
import './App.css';
import TraceTextField from './TraceTextField';
import FormulaTextField from './FormulaTextField';
import MeasureSelect from './MeasureSelect';

function App() {
  return (
    <div class="flexbox-container">
      <div>
        <TraceTextField />
      </div>
      <div>
        <FormulaTextField />
        <MeasureSelect />
      </div>
    </div>
  );
}

export default App;
