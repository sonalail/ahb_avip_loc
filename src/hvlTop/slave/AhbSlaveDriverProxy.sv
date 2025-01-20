`ifndef AHB_SLAVE_DRIVER_PROXY_INCLUDED_
`define AHB_SLAVE_DRIVER_PROXY_INCLUDED_

//--------------------------------------------------------------------------------------------
//  Class: ahb_slave_driver_proxy
//  This is the proxy driver on the HVL side
//  It receives the transactions and converts them to task calls for the HDL driver
//--------------------------------------------------------------------------------------------
class AhbSlaveDriverProxy extends uvm_driver#(AhbSlaveTransaction);
  `uvm_component_utils(AhbSlaveDriverProxy)

  //Variable : AhbSlaveTransaction_h
  //Declaring handle for apb slave transaction
  AhbSlaveTransaction ahb_slave_tx_h;

  // Variable: apb_slave_driver_bfm_h;
  // Handle for apb_slave driver bfm
  virtual AhbSlaveDriverBfm ahb_slave_drv_bfm_h;

  // Variable: apb_slave_agent_cfg_h;
  // Handle for apb_slave agent configuration
  AhbSlaveAgentConfig ahb_slave_agent_cfg_h;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbSlaveDriverProxy", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern virtual task check_for_pslverr(inout apb_transfer_char_s struct_packet);
  extern virtual task task_write(inout apb_transfer_char_s struct_packet);
  extern virtual task task_read(inout apb_transfer_char_s struct_packet);
endclass : AhbSlaveDriverProxy
  
//--------------------------------------------------------------------------------------------
//  Construct: new
//  Initializes memory for new object
//
//  Parameters:
//  name - AhbSlaveDriverProxy
//  parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function AhbSlaveDriverProxy::new(string name = "AhbSlaveDriverProxy", uvm_component parent = null);
  super.new(name, parent);
endfunction : new

//--------------------------------------------------------------------------------------------
//  Function: build_phase
//  Slave_driver_bfm congiguration is obtained in build phase
//
//  Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void AhbSlaveDriverProxy::build_phase(uvm_phase phase);
  super.build_phase(phase);
  if(!uvm_config_db #(virtual AhbSlaveDriverBfm)::get(this,"","AhbSlaveDriverBfm",
                                                             ahb_slave_drv_bfm_h)) begin
    `uvm_fatal("FATAL_SDP_CANNOT_GET_SLAVE_DRIVER_BFM","cannot get() ahb_slave_drv_bfm_h");
  end

endfunction : build_phase

//--------------------------------------------------------------------------------------------
//  Function: connect_phase
//  Connects driver_proxy and driver_bfm
//
//  Parameters:
//  phase - stores the current phase
//--------------------------------------------------------------------------------------------
function void AhbSlaveDriverProxy::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
endfunction : connect_phase


//-------------------------------------------------------
// Function: end_of_elaboration_phase
//Description: connects driver_proxy and driver_bfm
//
// Parameters:
//  phase - stores the current phase
//-------------------------------------------------------
function void AhbSlaveDriverProxy::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);
  ahb_slave_drv_bfm_h.ahb_slave_drv_proxy_h = this;
endfunction : end_of_elaboration_phase

//--------------------------------------------------------------------------------------------
// Task: run_phase
// Gets the sequence_item, converts them to struct compatible transactions
// and sends them to the BFM to drive the data over the interface
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
task AhbSlaveDriverProxy::run_phase(uvm_phase phase);
  
  //wait for system reset
  ahb_slave_drv_bfm_h.wait_for_preset_n();
  `uvm_info(get_type_name(), $sformatf("INSIDE run phase "),UVM_LOW);
 
  forever begin
    
    
    seq_item_port.get_next_item(req);
  
    seq_item_port.item_done();

  end
endtask : run_phase

//--------------------------------------------------------------------------------------------
// Task: task_write
// This task is used to write the data into the slave memory
// Parameters:
//  struct_packet   - apb_transfer_char_s
//--------------------------------------------------------------------------------------------
task AhbSlaveDriverProxy::task_write(inout apb_transfer_char_s struct_packet);

endtask : task_write

//--------------------------------------------------------------------------------------------
// Task: task_read
// This task is used to read the data from the slave memory
// Parameters:
//  struct_packet   - apb_transfer_char_s
//--------------------------------------------------------------------------------------------
task AhbSlaveDriverProxy::task_read(inout apb_transfer_char_s struct_packet);

endtask : task_read

//--------------------------------------------------------------------------------------------
// Task: check_for_pslverr
// Gets the struct packet and sends it to slave agent config to check the correct address 
// of the slave is selected
//
// Parameters:
//  struct_packet   - apb_transfer_char_s
//--------------------------------------------------------------------------------------------
task AhbSlaveDriverProxy::check_for_pslverr(inout apb_transfer_char_s struct_packet);

endtask : check_for_pslverr 

`endif
