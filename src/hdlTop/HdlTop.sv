`ifndef HDLTOP_INCLUDED
`define HDLTOP_INCLUDED

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

  //Variable : hclk
  //Declaration of system clock
  bit hclk;

  //Variable : hresetn
  //Declaration of system reset
  bit hresetn;

  //-------------------------------------------------------
  // Generation of system clock at frequency rate of 20ns
  //-------------------------------------------------------
  initial begin
   hclk = 1'b0;
    forever #10 hclk =!hclk;
  end

  //-------------------------------------------------------
  // Generation of system reset signal,
  //  system reset can be asserted asynchronously,
  //  but system reset de-assertion is synchronous.
  //-------------------------------------------------------
  initial begin
    hresetn = 1'b1;
    #15 hresetn= 1'b0;

    repeat(1) begin
      @(posedge hclk);
    end
    hresetn = 1'b1;
  end

  //-------------------------------------------------------
  // AHB Interface Instantiation
  //-------------------------------------------------------
  AhbInterface ahbInterface(hclk,hresetn);

  //-------------------------------------------------------
  // AHB Master BFM Agent Instantiation
  //-------------------------------------------------------
  AhbMasterAgentBFM ahbMasterAgentBFM(ahbInterface); 
  
  //-------------------------------------------------------
  // AHB Slave BFM Agent Instantiation
  //-------------------------------------------------------
 

endmodule : HdlTop

`endif
