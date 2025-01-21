`ifndef AHBMASTERDRIVERBFM_INCLUDED_
`define AHBMASTERDRIVERBFM_INCLUDED_

//-------------------------------------------------------
// Importing ahb global package
//-------------------------------------------------------
import AhbGlobalPackage::*;

//--------------------------------------------------------------------------------------------
// Interface : AhbMasterDriverBFM
//  Used as the HDL driver for ahb
//  It connects with the HVL driver_proxy for driving the stimulus
//--------------------------------------------------------------------------------------------
interface AhbMasterDriverBFM (input  bit  HCLK,
                              input  bit  HRESETn,
                              input logic [ADDR_WIDTH-1:0] HADDR;
                              input logic [2:0] HBURST;
                              input logic HMASTLOCK;
                              input logic [HPROT_WIDTH-1:0] HPROT;
                              input logic [2:0] HSIZE;
                              input logic HNONSEC;
                              input logic HEXCL;
                              input logic [HMASTER_WIDTH-1:0] HMASTER;
                              input logic [1:0] HTRANS;     
                              input logic HWRITE;
                              input logic [DATA_WIDTH-1:0] HWDATA;
                              output logic [DATA_WIDTH-1:0] HRDATA;
                              output logic HREADY;
                              output logic HREADYOUT;
                              output logic HRESP;
                              output logic HEXOKAY;
                              );

  //-------------------------------------------------------
  // Importing uvm package file
  //-------------------------------------------------------
  import AhbMasterPackage::*;
  `include "uvm_macros.svh"
  
  //-------------------------------------------------------
  // Importing the master package file
  //-------------------------------------------------------
  import AhbMasterPackage::*;
  
  //Variable: name
  //Used to store the name of the interface
  string name = "AHB_MASTER_DRIVER_BFM"; 
  
  //Variable: ahb_master_drv_proxy_h
  //Creating the handle for the proxy_driver
  AhbMasterDriverProxy ahbMasterDriverProxy;
   
  //-------------------------------------------------------
  // Used to display the name of the interface
  //-------------------------------------------------------
  initial begin
    `uvm_info(name, $sformatf(name),UVM_LOW)
  end
 
  //-------------------------------------------------------
  // Task: waitForHRESETn
  //  Waiting for the system reset to be active low
  //-------------------------------------------------------
  task waitForHRESETn();
    @(negedge HRESETn);
    `uvm_info(name ,$sformatf("SYSTEM RESET DETECTED"),UVM_HIGH)
 
   @(posedge HRESETn);
    `uvm_info(name ,$sformatf("SYSTEM RESET DEACTIVATED"),UVM_HIGH)
  endtask: waitForHRESETn
  
  //--------------------------------------------------------------------------------------------
  // Task: driveToBFM
  //  This task will drive the data from bfm to proxy using converters
  //
  // Parameters:
  // dataPacket - handle for ahbTransferCharStruct
  // configPacket - handle for ahbTransferConfigStruct
  //--------------------------------------------------------------------------------------------
  task driveToBFM(inout ahbTransferCharStruct dataPacket, input ahbTransferConfigStruct configPacket);
    `uvm_info(name,$sformatf("dataPacket = \n%p",dataPacket),UVM_HIGH);
    `uvm_info(name,$sformatf("configPacket = \n%p",configPacket),UVM_HIGH);
    `uvm_info(name,$sformatf("DRIVE TO BFM TASK"),UVM_HIGH);

    //logic to be written

  endtask: driveToBFM

 

endinterface : AhbMasterDriverBFM

`endif
