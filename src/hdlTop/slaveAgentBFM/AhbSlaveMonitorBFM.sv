 `ifndef AHBSLAVEMONITORBFM_INCLUDED_
`define AHBSLAVEMONITORBFM_INCLUDED_

//-------------------------------------------------------
// Importing apb global package
//-------------------------------------------------------
import ahb_global_pkg::*;

//--------------------------------------------------------------------------------------------
// Inteface: AhbSlaveMonitorBFM
//  Connects the slave monitor bfm with the monitor proxy 
//  to call the tasks and functions from apb monitor bfm to apb monitor proxy
//--------------------------------------------------------------------------------------------
interface AhbSlaveMonitorBFM (input  bit   HCLK,
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
  string name = "AHB_SLAVE_MONITOR_BFM";
  

  //Variable: ahb_slave_drv_proxy_h
  //Declaring handle for AhbSlaveDriverProxy
  
  AhbSlaveMonitorProxy ahbSlaveMonitorProxy;
  

  //-------------------------------------------------------
  // Used to display the name of the interface
  //-------------------------------------------------------
  initial begin
    `uvm_info(name,$sformatf(name),UVM_LOW);
  end

  //-------------------------------------------------------
  // Task: wait_for_HRESETn
  //  Waiting for the system reset to be active low
  //-------------------------------------------------------
  task waitForHRESETn();
    @(negedge HRESETn);
    `uvm_info(name, $sformatf("SYSTEM_RESET_DETECTED"), UVM_HIGH)
    
    @(posedge HRESETn);
    `uvm_info(name, $sformatf("SYSTEM_RESET_DEACTIVATED"), UVM_HIGH)
  endtask : waitForHRESETn

  //-------------------------------------------------------
  // Task: sampleData
  //  In this task, the pwdata and prdata is sampled
  //
  // Parameters: 
  //  ahbDataPacket - Handle for ahbTransferCharStruct class 
  //  ahbConfigPacket  - Handle for ahbTransferCharStruct class
  //-------------------------------------------------------
  task sampleData (output ahbTransferCharStruct ahbDataPacket, input ahbTransferCharStruct ahbConfigPacket);
    //logic to be written
  endtask : sampleData

endinterface : AhbSlaveMonitorBfm 

`endif
