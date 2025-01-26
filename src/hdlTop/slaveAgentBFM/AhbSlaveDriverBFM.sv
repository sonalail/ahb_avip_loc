`ifndef AHBSLAVEDRIVERBFM_INCLUDED_
`define AHBSLAVEDRIVERBFM_INCLUDED_

import AhbGlobalPackage::*;

interface AhbSlaveDriverBFM (input  bit   hclk,
                              input  bit  hresetn,
                              input logic [ADDR_WIDTH-1:0] haddr,
                              input logic [2:0] hburst,
                              input logic hmastlock,
                              input logic [HPROT_WIDTH-1:0] hprot,
                              input logic [2:0] hsize,
                              input logic hnonsec,
                              input logic hexcl,
                              input logic [HMASTER_WIDTH-1:0] hmaster,
                              input logic [1:0] htrans,    
                              input logic hwrite,
                              input logic [DATA_WIDTH-1:0] hwdata,
                              input logic [(DATA_WIDTH/8)-1:0]hwstrb,
                              output logic [DATA_WIDTH-1:0] hrdata,
                              output logic hready,
                              output logic hreadyout,
                              output logic hresp,
                              output logic hexokay,
                             input logic [NO_OF_SLAVES-1:0]hselx
                            );

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  import AhbSlavePackage::*;
 
  string name = "AHB_SLAVE_DRIVER_BFM";

  AhbSlaveDriverProxy ahbSlaveDriverProxy ;

  initial begin
    `uvm_info(name,$sformatf(name),UVM_LOW);
  end

  task waitForResetn();

    @(negedge hresetn);
    `uvm_info(name,$sformatf("SYSTEM RESET DETECTED"),UVM_HIGH)
    @(posedge hresetn);
    `uvm_info(name,$sformatf("SYSTEM RESET DEACTIVATED"),UVM_HIGH)
  
  endtask: waitForResetn

  task waitForSetupState(output ahbTransferCharStruct dataPacket);
  //logic
  endtask:waitForSetupState

  task waitForAccessState(inout ahbTransferCharStruct dataPacket);
   //logic
  endtask: waitForAccessState

endinterface : AhbSlaveDriverBFM

`endif
