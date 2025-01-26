`ifndef HDLTOP_INCLUDED
`define HDLTOP_INCLUDED

module HdlTop;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  import AhbGlobalPackage::*;

  initial begin
    `uvm_info("HDL_TOP","HDL_TOP",UVM_LOW);
  end

  bit hclk;

  bit hresetn;

  initial begin
   hclk = 1'b0;
    forever #10 hclk =!hclk;
  end

  initial begin
    hresetn = 1'b1;
    #15 hresetn= 1'b0;

    repeat(1) begin
      @(posedge hclk);
    end
    hresetn = 1'b1;
  end

 AhbInterface ahbInterface(hclk,hresetn);

 AhbMasterAgentBFM ahbMasterAgentBFM(ahbInterface); 

 AhbSlaveAgentBFM ahbSlaveAgentBFM(ahbInterface); 

endmodule : HdlTop

`endif
