 `ifndef AHBSLAVEMONITORBFM_INCLUDED_
`define AHBSLAVEMONITORBFM_INCLUDED_

//-------------------------------------------------------
// Importing apb global package
//-------------------------------------------------------
import AhbGlobalPackage::*;

//--------------------------------------------------------------------------------------------
// Inteface: AhbSlaveMonitorBFM
//  Connects the slave monitor bfm with the monitor proxy 
//  to call the tasks and functions from apb monitor bfm to apb monitor proxy
//--------------------------------------------------------------------------------------------
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
                              output logic [DATA_WIDTH-1:0] hrdata,
                              output logic hready,
                              output logic hreadyout,
                              output logic hresp,
                              output logic hexokay,
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
  // Task: waitForResetn
  //  Waiting for the system reset to be active low
  //-------------------------------------------------------
  task waitForResetn();
   @(negedge hresetn);
    `uvm_info(name, $sformatf("SYSTEM_RESET_DETECTED"), UVM_HIGH)
    
    @(posedge hresetn);
    `uvm_info(name, $sformatf("SYSTEM_RESET_DEACTIVATED"), UVM_HIGH)
  endtask : waitForResetn

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
