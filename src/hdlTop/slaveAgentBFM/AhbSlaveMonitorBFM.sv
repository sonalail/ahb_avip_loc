 `ifndef AHBSLAVEMONITORBFM_INCLUDED_
`define AHBSLAVEMONITORBFM_INCLUDED_

import AhbGlobalPackage::*;

interface AhbSlaveMonitorBFM (input  bit   hclk,
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

  string name = "AHB_SLAVE_MONITOR_BFM";

  AhbSlaveMonitorProxy ahbSlaveMonitorProxy;

  initial begin
    `uvm_info(name,$sformatf(name),UVM_LOW);
  end

  task waitForResetn();
   @(negedge hresetn);
    `uvm_info(name, $sformatf("SYSTEM_RESET_DETECTED"), UVM_HIGH)
    
    @(posedge hresetn);
    `uvm_info(name, $sformatf("SYSTEM_RESET_DEACTIVATED"), UVM_HIGH)
  endtask : waitForResetn

 task sampleData (output ahbTransferCharStruct ahbDataPacket, input ahbTransferConfigStruct ahbConfigPacket);
    //logic to be written
  endtask : sampleData

endinterface : AhbSlaveMonitorBFM

`endif
