
`ifndef AHBMASTERMONITORBFM_INCLUDED_
`define AHBMASTERMONITORBFM_INCLUDED_

//-------------------------------------------------------
// Importing ahb global package
//-------------------------------------------------------
import AhbGlobalPackage::*;

//--------------------------------------------------------------------------------------------
// Interface: AhbMasterMonitorBFM
//  Connects the master monitor bfm with the master monitor proxy
//--------------------------------------------------------------------------------------------
interface AhbMasterMonitorBFM(
    input logic [ADDR_WIDTH-1:0] HADDR,
    input logic [NO_OF_SLAVES-1:0] HSELx,
    input logic [2:0] HBURST,
    input logic HMASTLOCK,
    input logic [HPROT_WIDTH-1:0] HPROT,
    input logic [2:0] HSIZE,
    input logic HNONSEC,
    input logic HEXCL,
    input logic [HMASTER_WIDTH-1:0] HMASTER,
    input logic [1:0] HTRANS,
    input logic [DATA_WIDTH-1:0] HWDATA,
    input logic [(DATA_WIDTH/8)-1:0] HWSTRB,
    input logic HWRITE,
    input logic [DATA_WIDTH-1:0] HRDATA,
    input logic HREADYOUT,
    input logic HRESP,
    input logic HEXOKAY,
    input logic HREADY
);
  //-------------------------------------------------------
  // Importing uvm package and AhbMasterPackage file
  //-------------------------------------------------------
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  //-------------------------------------------------------
  // Importing global package
  //-------------------------------------------------------
  import AhbMasterPackage::*;

  // Variable: ahbMasterMonitorProxy
  // Declaring handle for AhbMasterMonitorProxy  
  AhbMasterMonitorProxy ahbMasterMonitorProxy;

  // Variable: name
  // Assigning the string used in infos
  string name = "AHB_MASTER_MONITOR_BFM"; 
 
  initial begin
    `uvm_info(name, $sformatf("AHB MASTER MONITOR BFM"), UVM_LOW);
  end

  //-------------------------------------------------------
  // Task: waitForRESETn
  //  Waiting for the system reset to be active low
  //-------------------------------------------------------
  task waitForRESETn();
    @(negedge HRESETn);
    `uvm_info(name, $sformatf("system reset detected"), UVM_HIGH)
    
    @(posedge HRESETn);
    `uvm_info(name, $sformatf("system reset deactivated"), UVM_HIGH)
  endtask : waitForRESETn
  
  //-------------------------------------------------------
  // Task: sampleData
  //  In this task, the HWDATA and HRDATA is sampled
  //
  // Parameters: 
  //  ahbDataPacket - Handle for ahbTransferCharStruct class
  //  ahbConfigPacket  - Handle for ahbTransferConfigStruct class
  //-------------------------------------------------------
    task sampleData (output ahbTransferCharStruct ahbDataPacket, input ahbTransferConfigStruct ahbConfigPacket);
   //logic to be written
    
  endtask : sampleData

endinterface : AhbMasterMonitorBFM

`endif
