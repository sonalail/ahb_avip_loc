`ifndef HVL_TOP_INCLUDED_
`define HVL_TOP_INCLUDED_

//--------------------------------------------------------------------------------------------
// Module : hvl_top
//  Starts the testbench components
//--------------------------------------------------------------------------------------------
module hvl_top;

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

endmodule : hvl_top

`endif
