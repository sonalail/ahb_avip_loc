`ifndef AHBSLAVEDRIVERPROXY_INCLUDED_
`define AHBSLAVEDRIVERPROXY_INCLUDED_

//--------------------------------------------------------------------------------------------
//  Class: AhbSlaveDriverProxy
//  This is the proxy driver on the HVL side
//  It receives the transactions and converts them to task calls for the HDL driver
//--------------------------------------------------------------------------------------------
class AhbSlaveDriverProxy extends uvm_driver#(AhbSlaveTransaction);
  `uvm_component_utils(AhbSlaveDriverProxy)

  //Variable : ahbSlaveTx
  //Declaring handle for apb slave transaction
  AhbSlaveTransaction ahbSlaveTx;

  // Variable: ahbSlaveDrvBFM;
  // Handle for apb_slave driver bfm
  virtual AhbSlaveDriverBFM ahbSlaveDrvBFM;

  // Variable: ahbSlaveAgentConfig;
  // Handle for apb Slave agent configuration
  AhbSlaveAgentConfig ahbSlaveAgentConfig;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbSlaveDriverProxy", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern virtual task checkForPslverr(inout apbTransferCharStruct structPacket);
  extern virtual task taskWrite(inout apbTransferCharStruct structPacket);
  extern virtual task taskRead(inout apbTransferCharStruct structPacket);
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
//  AhbSlaveDriverBFM congiguration is obtained in build phase
//
//  Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void AhbSlaveDriverProxy::build_phase(uvm_phase phase);
  super.build_phase(phase);
  if(!uvm_config_db #(virtual AhbSlaveDriverBFM)::get(this,"","AhbSlaveDriverBFM",
                                                             ahbSlaveDrvBFM)) begin
    `uvm_fatal("FATAL SDP CANNOT GET SLAVE DRIVER BFM","cannot get() ahbSlaveDrvBFM");
  end

endfunction : build_phase

//--------------------------------------------------------------------------------------------
//  Function: connect_phase
//  Connects driver proxy and driver bfm
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
  ahbSlaveDrvBFM.ahbSlaveDrvProxy = this;
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
  ahbSlaveDrvBFM.wait_for_preset_n();
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
    task AhbSlaveDriverProxy::taskWrite(inout apbTransferCharStruct structPacket);

endtask : taskWrite

//--------------------------------------------------------------------------------------------
// Task: task_read
// This task is used to read the data from the slave memory
// Parameters:
//  struct_packet   - apb_transfer_char_s
//--------------------------------------------------------------------------------------------
    task AhbSlaveDriverProxy::taskRead(inout apbTransferCharStruct structPacket);

endtask : taskRead

//--------------------------------------------------------------------------------------------
// Task: check_for_pslverr
// Gets the struct packet and sends it to slave agent config to check the correct address 
// of the slave is selected
//
// Parameters:
//  struct_packet   - apb_transfer_char_s
//--------------------------------------------------------------------------------------------
    task AhbSlaveDriverProxy::checkForPslverr(inout apbTransferCharStruct structPacket);

endtask : checkForPslverr 

`endif
