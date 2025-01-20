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
   
  //Variable: state
  //Creating handle for fsm states
  ahb_fsm_state_e state;

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
   
    `uvm_info(name ,$sformatf("SYSTEM RESET DETECTED"),UVM_HIGH)
 
   
    `uvm_info(name ,$sformatf("SYSTEM RESET DEACTIVATED"),UVM_HIGH)
  endtask: wait_for_preset_n
  
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

    //Driving Setup state
    drive_setup_state(data_packet);

    //Driving Access state
    waiting_in_access_state(data_packet);

  endtask: drive_to_bfm

  //--------------------------------------------------------------------------------------------
  // Task: drive_idle_state
  //  This task drives the ahb interface to idle state
  //--------------------------------------------------------------------------------------------
  task drive_idle_state();
  
    `uvm_info(name,$sformatf("DROVE THE IDLE STATE"),UVM_HIGH)

    `uvm_info("DEBUG_MSHA", $sformatf("drive_ahb_idle state = %0s and state = %0d",
                                    state.name(), state), UVM_NONE);
    
  endtask : drive_idle_state

  //--------------------------------------------------------------------------------------------
  // Task: drive_setup_state
  //  It drives the required signals to the slave 
  //
  // Parameters:
  //  data_packet - ahb_transfer_char_s
  //--------------------------------------------------------------------------------------------
  task drive_setup_state(inout ahb_transfer_char_s data_packet);
   
    `uvm_info(name,$sformatf("DRIVING THE SETUP STATE"),UVM_HIGH)
   
    `uvm_info("DEBUG_MSHA", $sformatf("drive_ahb_setup state = %0s and state = %0d", state.name(), state), UVM_NONE);
    
  endtask : drive_setup_state
 
  //-------------------------------------------------------
  // Task: drive_access_state
  //  This task defines the accessing of data signals from 
  //  master to slave or viceverse
  //
  // Parameters:
  //  data_packet - handle for ahb_transfer_char_s
  //-------------------------------------------------------
  task waiting_in_access_state(inout ahb_transfer_char_s data_packet);
   
    `uvm_info(name,$sformatf("INSIDE ACCESS STATE"),UVM_HIGH);

   
    
    `uvm_info("DEBUG_NADEEM",$sformatf("pready=%0d",pready), UVM_HIGH);

  
  endtask : waiting_in_access_state

  //--------------------------------------------------------------------------------------------
  // Task: detect_wait_state
  // In this task, signals are waiting for pready to set to high to transfer the data_packet
  //
  // Parameters:
  // data_packet - handle for ahb_transfer_char_s
  //--------------------------------------------------------------------------------------------
  task detect_wait_state(inout ahb_transfer_char_s data_packet);
 
    `uvm_info(name,$sformatf("DETECT_WAIT_STATE"),UVM_HIGH);

   
    
    `uvm_info(name,$sformatf("DATA READY TO TRANSFER"),UVM_HIGH);

 
  endtask : detect_wait_state

endinterface : ahb_master_driver_bfm

`endif
