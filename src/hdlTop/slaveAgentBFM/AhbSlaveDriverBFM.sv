`ifndef AHBSLAVEDRIVERBFM_INCLUDED_
`define AHBSLAVEDRIVERBFM_INCLUDED_

//-------------------------------------------------------
// Importing ahb global package
//-------------------------------------------------------
import AhbGlobalPackage::*;

//--------------------------------------------------------------------------------------------
// Interface : AhbSlaveDriverBFm
//  Used as the HDL driver for ahb
//  It connects with the HVL driver_proxy for driving the stimulus
//--------------------------------------------------------------------------------------------
interface AhbSlaveDriverBFM (input  bit   HCLK,
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
  // Importing uvm package
  //-------------------------------------------------------
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  
  //-------------------------------------------------------
  // Importing slave driver proxy
  //------------------------------------------------------- 
  import AhbSlavePackage::*;
  
  //Variable : name
  //Used to store the name of the interface
  string name = "AHB_SLAVE_DRIVER_BFM";
  

  //Variable: ahbSlaveDriverProxy 
  //Declaring handle for AhbSlaveDriverProxy
  
  AhbSlaveDriverProxy ahbSlaveDriverProxy ;
  

  //-------------------------------------------------------
  // Used to display the name of the interface
  //-------------------------------------------------------
  initial begin
    `uvm_info(name,$sformatf(name),UVM_LOW);
  end

  //-------------------------------------------------------
  // Task: waitForHRESETn
  // Waiting for the system reset to be active low
  //-------------------------------------------------------
  task waitForHRESETn();

    @(negedge HRESETn);
    `uvm_info(name,$sformatf("SYSTEM RESET DETECTED"),UVM_HIGH)
    @(posedge HRESETn);
    `uvm_info(name,$sformatf("SYSTEM RESET DEACTIVATED"),UVM_HIGH)
  
  endtask: waitForHRESETn
  
  //-------------------------------------------------------
  // Task: waitForSetupState
  // Samples the required data and sends back to the proxy
  //-------------------------------------------------------
  task waitForSetupState(output ahbTransferCharStruct dataPacket);
  //logic
  endtask:waitForSetupState

  //-------------------------------------------------------
  // Task: wait_for_access_state
  // Samples the data or drives the data to master based
  // on pwrite signal
  //-------------------------------------------------------
  task waitForAccessState(inout ahbTransferCharStruct dataPacket);
   //logic
  endtask: waitForAccessState

endinterface : AhbSlaveDriverBFM

`endif
