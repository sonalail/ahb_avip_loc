`ifndef HDL_TOP_INCLUDED
`define HDL_TOP_INCLUDED

//--------------------------------------------------------------------------------------------
// Module      : HDL Top
// Description : Has a interface and slave agent bfm.
//--------------------------------------------------------------------------------------------
module HdlTop;

  //-------------------------------------------------------
  // Importing uvm package and Including uvm macros file
  //-------------------------------------------------------
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  
  //-------------------------------------------------------
  // Importing apb global package
  //-------------------------------------------------------
  import AhbGlobalPackage::*;

  initial begin
    `uvm_info("HDL_TOP","HDL_TOP",UVM_LOW);
  end

  //Variable : HCLK
  //Declaration of system clock
  bit HCLK;

  //Variable : HRESETn
  //Declaration of system reset
  bit HRESETn;

  //-------------------------------------------------------
  // Generation of system clock at frequency rate of 20ns
  //-------------------------------------------------------
  initial begin
    HCLK = 1'b0;
    forever #10 HCLK =!HCLK;
  end

  //-------------------------------------------------------
  // Generation of system preset_n
  //  system reset can be asserted asynchronously,
  //  but system reset de-assertion is synchronous.
  //-------------------------------------------------------
  initial begin
    HRESETn = 1'b1;
    #15 HRESETn= 1'b0;

    repeat(1) begin
      @(posedge HCLK);
    end
    HRESETn = 1'b1;
  end

  //-------------------------------------------------------
  // AHB Interface Instantiation
  //-------------------------------------------------------
  AhbInterface intf(HCLK,HRESETn);

  //-------------------------------------------------------
  // AHB Master BFM Agent Instantiation
  //-------------------------------------------------------
  AhbMasterAgentBfm apb_master_agent_bfm_h(intf); 
  
  //-------------------------------------------------------
  // AHB Slave BFM Agent Instantiation
  //-------------------------------------------------------
  genvar i;
  generate
    for (i=0; i < NO_OF_SLAVES; i++) begin : AhbSlaveAgentBfm
      AhbSlaveAgentBfm #(.SLAVE_ID(i)) apb_slave_agent_bfm_h(intf);
      defparam AhbSlaveAgentBfm[i].apb_slave_agent_bfm_h.SLAVE_ID = i;
    end
  endgenerate

endmodule : hdl_top

`endif
