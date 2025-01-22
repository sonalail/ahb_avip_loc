
`ifndef AHBMASTERDRIVERPROXY_INCLUDED_
`define AHBMASTERDRIVERPROXY_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: ahbMasterDriverProxy
//  Driver is written by extending uvm_driver,uvm_driver is inherited from uvm_component,
//  Methods and TLM port (seq_item_port) are defined for communication between sequencer and driver,
//  uvm_driver is a parameterized class and it is parameterized with the type of the request
//  sequence_item and the type of the response sequence_item
//--------------------------------------------------------------------------------------------
class AhbMasterDriverProxy extends uvm_driver #(AhbMasterTransaction);
  `uvm_component_utils(AhbMasterDriverProxy)

  //Variable: ahbMasterTransaction
  //Declaring handle for ahbMasterTransaction
  AhbMasterDriverProxy   ahbMasterDriverProxy;

  //Variable: ahbMasterDriverTransaction;
  //Declaring handle for ahbMasterDriverBFM
  virtual AhbMasterDriverBFM ahbMasterDriverBFM;

  //Variable: ahbMasterAgentConfig
  //Declaring handle for AhbMasterAgentConfig class

  AhbMasterAgentConfig ahbMasterAgentConfig;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbMasterDriverProxy", uvm_component parent);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);

endclass : AhbMasterDriverProxy

//--------------------------------------------------------------------------------------------
// Construct: new
// Initializes memory for new object
//
// Parameters:
// name - AhbMasterDriverProxy
// parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function AhbMasterDriverProxy::new(string name = "AhbMasterDriverProxy",uvm_component parent);
  super.new(name, parent);
endfunction : new

//--------------------------------------------------------------------------------------------
// Function: build_phase
//  Creates the required ports, gets the required configuration from confif_db
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void AhbMasterDriverProxy::build_phase(uvm_phase phase);
  super.build_phase(phase);
  if(!uvm_config_db #(virtual AhbMasterDriverBFM)::get(this,"","AhbMasterDriverBFM", ahbMasterDriverBFM)) begin
    `uvm_fatal("FATAL_MDP_CANNOT_GET_APB_MASTER_DRIVER_BFM","cannot get() ahbMasterDriverBFM");
  end
endfunction : build_phase

//--------------------------------------------------------------------------------------------
// Function: connect_phase
//  Connecting ahb_master driver handle with ahb_master agent config
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void AhbMasterDriverProxy::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
endfunction : connect_phase

//--------------------------------------------------------------------------------------------
// Function: end_of_elaboration_phase
// Pointing handle of driver proxy in HDL BFM to this proxy method in HVL part
//
// Parameters:
// phase - uvm phase
//--------------------------------------------------------------------------------------------
function void AhbMasterDriverProxy::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);
  ahbMasterDriverBFM.ahbMasterDriverProxy = this;

endfunction : end_of_elaboration_phase

//--------------------------------------------------------------------------------------------
// Task: run_phase
// Gets the sequence_item, converts them to struct compatible transactions
// and sends them to the BFM to drive the data over the interface
//
// Parameters:
// phase - uvm phase
//--------------------------------------------------------------------------------------------
task AhbMasterDriverProxy::run_phase(uvm_phase phase);

  //wait for system reset
  ahbMasterDriverBFM.waitForHRESETn();

uvm_info(get_type_name(), $sformatf(" run phase inside master driver proxy \n "), UVM_NONE);


  forever begin
    seq_item_port.get_next_item(req);

    `uvm_info(get_type_name(), $sformatf("AFTER :: inside master driver proxy \n "), UVM_NONE);

    seq_item_port.item_done();
  end

endtask : run_phase

`endif
