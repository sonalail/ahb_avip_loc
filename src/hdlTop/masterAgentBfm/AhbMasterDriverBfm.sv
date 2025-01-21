`ifndef AHB_MASTER_DRIVER_BFM_INCLUDED_
`define AHB_MASTER_DRIVER_BFM_INCLUDED_

//-------------------------------------------------------
// Importing ahb global package
//-------------------------------------------------------
import AhbGlobalPackage::*;

//--------------------------------------------------------------------------------------------
// Interface : AhbMasterDriverBfm
//  Used as the HDL driver for ahb
//  It connects with the HVL driver_proxy for driving the stimulus
//--------------------------------------------------------------------------------------------
interface AhbMasterDriverBfm (input  bit   HCLK,
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
  AhbMasterDriverProxy ahb_master_drv_proxy_h;
   
  //-------------------------------------------------------
  // Used to display the name of the interface
  //-------------------------------------------------------
  initial begin
    `uvm_info(name, $sformatf(name),UVM_LOW)
  end
 
  //-------------------------------------------------------
  // Task: wait_for_HRESETn
  //  Waiting for the system reset to be active low
  //-------------------------------------------------------
  task wait_for_HRESETn();
    @(negedge HRESETn);
    `uvm_info(name ,$sformatf("SYSTEM RESET DETECTED"),UVM_HIGH)
 
   @(posedge HRESETn);
    `uvm_info(name ,$sformatf("SYSTEM RESET DEACTIVATED"),UVM_HIGH)
  endtask: wait_for_HRESETn
  
  //--------------------------------------------------------------------------------------------
  // Task: drive_to_bfm
  //  This task will drive the data from bfm to proxy using converters
  //
  // Parameters:
  // data_packet - handle for ahb_transfer_char_s
  // cfg_pkt     - handle for ahb_transfer_cfg_s
  //--------------------------------------------------------------------------------------------
  task drive_to_bfm(inout ahb_transfer_char_s data_packet, input ahb_transfer_cfg_s cfg_packet);
    `uvm_info(name,$sformatf("data_packet=\n%p",data_packet),UVM_HIGH);
    `uvm_info(name,$sformatf("cfg_packet=\n%p",cfg_packet),UVM_HIGH);
    `uvm_info(name,$sformatf("DRIVE TO BFM TASK"),UVM_HIGH);

    //logic to be written

  endtask: drive_to_bfm

 

endinterface : ahb_master_driver_bfm

`endif
