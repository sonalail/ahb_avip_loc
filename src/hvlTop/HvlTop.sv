`ifndef HVLTOP_INCLUDED_
`define HVLTOP_INCLUDED_

//--------------------------------------------------------------------------------------------
// Module : HvlTop
//  Starts the testbench components
//--------------------------------------------------------------------------------------------
module HvlTop;

  //-------------------------------------------------------
  // Importing UVM Package and test Package
  //-------------------------------------------------------
  import uvm_pkg::*;
  import AhbBaseTestPackage::*;
  
  //-------------------------------------------------------
  // Calling run_test for simulation
  //-------------------------------------------------------
  initial begin
    run_test("AhbBaseTest");
  end

endmodule : HvlTop

`endif
