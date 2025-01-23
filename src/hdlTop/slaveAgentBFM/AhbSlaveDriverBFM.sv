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
                              output logic [DATA_WIDTH-1:0] hrdata,
                              output logic hready,
                              output logic hreadyout,
                              output logic hresp,
                              output logic hexokay
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
  // Task: waitForResetn
  // Waiting for the system reset to be active low
  //-------------------------------------------------------
  task waitForResetn();

    @(negedge hresetn);
    `uvm_info(name,$sformatf("SYSTEM RESET DETECTED"),UVM_HIGH)
    @(posedge hresetn);
    `uvm_info(name,$sformatf("SYSTEM RESET DEACTIVATED"),UVM_HIGH)
  
  endtask: waitForResetn
  
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
  // on hwrite signal
  //-------------------------------------------------------
  task waitForAccessState(inout ahbTransferCharStruct dataPacket);
   //logic
  endtask: waitForAccessState

endinterface : AhbSlaveDriverBFM

`endif
