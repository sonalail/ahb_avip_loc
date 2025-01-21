
`ifndef AHB_MASTER_MONITOR_BFM_INCLUDED_
`define AHB_MASTER_MONITOR_BFM_INCLUDED_

//-------------------------------------------------------
// Importing ahb global package
//-------------------------------------------------------
import AhbGlobalPackage::*;

//--------------------------------------------------------------------------------------------
// Interface: ahb_master_monitor_bfm
//  Connects the master monitor bfm with the master monitor proxy
//--------------------------------------------------------------------------------------------
interface AhbMasterMonitorBfm(
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

  // Variable: ahb_master_mon_proxy_h
  // Declaring handle for apb_master_monitor_proxy  
  AhbMasterMonitorProxy ahb_master_mon_proxy_h;

  // Variable: name
  // Assigning the string used in infos
  string name = "AHB_MASTER_MONITOR_BFM"; 
 
  initial begin
    `uvm_info(name, $sformatf("AHB MASTER MONITOR BFM"), UVM_LOW);
  end

  //-------------------------------------------------------
  // Task: wait_for_HRESETn
  //  Waiting for the system reset to be active low
  //-------------------------------------------------------
  task wait_for_HRESETn();
    @(negedge HRESETn);
    `uvm_info(name, $sformatf("system reset detected"), UVM_HIGH)
    
    @(posedge HRESETn);
    `uvm_info(name, $sformatf("system reset deactivated"), UVM_HIGH)
  endtask : wait_for_HRESETn
  
  //-------------------------------------------------------
  // Task: sample_data
  //  In this task, the pwdata and prdata is sampled
  //
  // Parameters: 
  //  ahb_data_packet - Handle for ahb_transfer_char_s class
  //  ahb_cfg_packet  - Handle for ahb_transfer_cfg_s class
  //-------------------------------------------------------
  task sample_data (output ahb_transfer_char_s ahb_data_packet, input ahb_transfer_cfg_s ahb_cfg_packet);
   //logic to be written
    
  endtask : sample_data

endinterface : AhbMasterMonitorBfm

`endif
