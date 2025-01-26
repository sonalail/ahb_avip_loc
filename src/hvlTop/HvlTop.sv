`ifndef HVLTOP_INCLUDED_
`define HVLTOP_INCLUDED_

module HvlTop;

  import uvm_pkg::*;
  import AhbBaseTestPackage::*;

  initial begin
    run_test("AhbBaseTest");
  end

endmodule : HvlTop

`endif
