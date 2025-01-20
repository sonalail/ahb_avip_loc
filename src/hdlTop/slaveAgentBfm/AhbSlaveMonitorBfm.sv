 `ifndef AHB_SLAVE_MONITOR_BFM_INCLUDED_
`define AHB_SLAVE_MONITOR_BFM_INCLUDED_

//-------------------------------------------------------
// Importing apb global package
//-------------------------------------------------------
import ahb_global_pkg::*;

//--------------------------------------------------------------------------------------------
// Inteface: apb_slave_monitor_bfm
//  Connects the slave monitor bfm with the monitor proxy 
//  to call the tasks and functions from apb monitor bfm to apb monitor proxy
//--------------------------------------------------------------------------------------------
interface AhbSlaveMonitorBfm (input  bit   HCLK,
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
  
  AhbSlaveMonitorProxy ahb_slave_mon_proxy_h;
  

  //-------------------------------------------------------
  // Used to display the name of the interface
  //-------------------------------------------------------
  initial begin
    `uvm_info(name,$sformatf(name),UVM_LOW);
  end

  //-------------------------------------------------------
  // Task: wait_for_preset_n
  //  Waiting for the system reset to be active low
  //-------------------------------------------------------
  task wait_for_preset_n();
    @(negedge preset_n);
    `uvm_info(name, $sformatf("SYSTEM_RESET_DETECTED"), UVM_HIGH)
    
    @(posedge preset_n);
    `uvm_info(name, $sformatf("SYSTEM_RESET_DEACTIVATED"), UVM_HIGH)
  endtask : wait_for_preset_n

  //-------------------------------------------------------
  // Task: sample_data
  //  In this task, the pwdata and prdata is sampled
  //
  // Parameters: 
  //  apb_data_packet - Handle for apb_transfer_char_s class
  //  apb_cfg_packet  - Handle for apb_transfer_cfg_s class
  //-------------------------------------------------------
  //task sample_data (output apb_transfer_char_s apb_data_packet, input apb_transfer_cfg_s apb_cfg_packet);
    //@(negedge pclk);
    
    //while(psel[apb_cfg_packet.slave_id] === 1'bX) begin
      //@(negedge pclk);
      //`uvm_info(name, $sformatf("Inside while loop PSEL"), UVM_HIGH)
    //end

    //while(psel[apb_cfg_packet.slave_id] !==1 || penable !==1 || pready !==1) begin
    //`uvm_info(name, $sformatf("Inside while loop: SLAVE[%0d] penable =%0d, pready=%0d, psel=%0d ", 
      //                        apb_cfg_packet.slave_id, penable, pready, psel), UVM_HIGH)
      //@(negedge pclk);
    //end
    //`uvm_info(name, $sformatf("After while loop: penable =%0d, pready=%0d, psel=%0d ", penable, pready, psel), UVM_HIGH)

    //apb_data_packet.pselx[0] = psel[apb_cfg_packet.slave_id];
    //apb_data_packet.pslverr  = pslverr;
    //apb_data_packet.pprot    = pprot;
    //apb_data_packet.pwrite   = pwrite;
    //apb_data_packet.paddr    = paddr;
    //apb_data_packet.pstrb    = pstrb;

    //if (pwrite == WRITE) begin
      //apb_data_packet.pwdata = pwdata;
    //end
    //else begin
      //apb_data_packet.prdata = prdata;
    //end
    //`uvm_info(name, $sformatf("SLAVE_SAMPLE_DATA=%p", apb_data_packet), UVM_HIGH)
  //endtask : sample_data

endinterface : AhbSlaveMonitorBfm 

`endif
