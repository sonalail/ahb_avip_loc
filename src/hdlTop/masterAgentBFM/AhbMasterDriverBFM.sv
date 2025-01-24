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
                              output logic [DATA_WIDTH-1:0] hrdata,
                              output logic hready,
                              output logic hreadyout,
                              output logic hresp,
                              output logic hexokay
                              );

  //-------------------------------------------------------
  // Importing uvm package file
  //-------------------------------------------------------
  import AhbMasterPackage::*;
  `include "uvm_macros.svh"
  import uvm_pkg::*; 
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
  // Task: waitForResetn
  //  Waiting for the system reset to be active low
  //-------------------------------------------------------
  task waitForResetn();
    @(negedge hresetn);
    `uvm_info(name ,$sformatf("SYSTEM RESET DETECTED"),UVM_HIGH)
 
   @(posedge hresetn);
    `uvm_info(name ,$sformatf("SYSTEM RESET DEACTIVATED"),UVM_HIGH)
  endtask:waitForResetn
  
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
