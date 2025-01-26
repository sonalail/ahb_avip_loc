`ifndef AHBMASTERDRIVERBFM_INCLUDED_
`define AHBMASTERDRIVERBFM_INCLUDED_

import AhbGlobalPackage::*;

interface AhbMasterDriverBFM (input  bit  hclk,
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

  import AhbMasterPackage::*;
  `include "uvm_macros.svh"
  import uvm_pkg::*; 

  import AhbMasterPackage::*;

  string name = "AHB_MASTER_DRIVER_BFM"; 
 
  AhbMasterDriverProxy ahbMasterDriverProxy;

  initial begin
    `uvm_info(name, $sformatf(name),UVM_LOW)
  end

  task waitForResetn();
    @(negedge hresetn);
    `uvm_info(name ,$sformatf("SYSTEM RESET DETECTED"),UVM_HIGH)
 
   @(posedge hresetn);
    `uvm_info(name ,$sformatf("SYSTEM RESET DEACTIVATED"),UVM_HIGH)
  endtask:waitForResetn

  task driveToBFM(inout ahbTransferCharStruct dataPacket, input ahbTransferConfigStruct configPacket);
    `uvm_info(name,$sformatf("dataPacket = \n%p",dataPacket),UVM_HIGH);
    `uvm_info(name,$sformatf("configPacket = \n%p",configPacket),UVM_HIGH);
    `uvm_info(name,$sformatf("DRIVE TO BFM TASK"),UVM_HIGH);

    //logic to be written

  endtask: driveToBFM

endinterface : AhbMasterDriverBFM

`endif
