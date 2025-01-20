`ifndef APB_SLAVE_MONITOR_PROXY_INCLUDED_
`define APB_SLAVE_MONITOR_PROXY_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbSlaveMonitorProxy
//  This is the HVL side AhbSlaveMonitorProxy
//  It gets the sampled data from the HDL slave monitor and converts them into transaction items
//--------------------------------------------------------------------------------------------
class AhbSlaveMonitorProxy extends uvm_monitor; 
  `uvm_component_utils(AhbSlaveMonitorProxy)
  
  // Variable: ahb_slave_mon_bfm_h
  // Declaring handle for ahb monitor bfm
  virtual AhbSlaveMonitorBfm ahb_slave_mon_bfm_h;
   
  // Variable: ahb_slave_agent_cfg_h
  // Declaring handle for AhbSlaveAgentConfig class 
  AhbSlaveAgentConfig ahb_slave_agent_cfg_h;
    
  // Variable: ahb_slave_analysis_port
  // Declaring analysis port for the monitor port
  uvm_analysis_port#(AhbSlaveTransaction) ahb_slave_analysis_port;
  
  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbSlaveMonitorProxy", uvm_component parent);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);

endclass : apb_slave_monitor_proxy

//--------------------------------------------------------------------------------------------
// Construct: new
//  Initializes memory for new object
//
// Parameters:
//  name   - AhbSlaveMonitorProxy
//  parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function AhbSlaveMonitorProxy::new(string name = "AhbSlaveMonitorProxy",uvm_component parent);
  super.new(name, parent);
  ahb_slave_analysis_port = new("ahb_slave_analysis_port",this);
endfunction : new

//--------------------------------------------------------------------------------------------
// Function: build_phase
//  Creates the required ports, gets the required configuration from confif_db
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void AhbSlaveMonitorProxy::build_phase(uvm_phase phase);
  super.build_phase(phase);
  if(!uvm_config_db #(virtual AhbSlaveMonitorBfm)::get(this,"","AhbSlaveMonitorBfm", ahb_slave_mon_bfm_h)) begin
    `uvm_fatal("FATAL_MDP_CANNOT_GET_AHB_SLAVE_MONITOR_BFM","cannot get() ahb_slave_mon_bfm_h");
  end
endfunction : build_phase

//--------------------------------------------------------------------------------------------
// Function: end_of_elaboration_phase
//  Pointing handle of monitor proxy in HDL BFM to this proxy method in HVL part
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void AhbSlaveMonitorProxy::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);
  ahb_slave_mon_bfm_h.ahb_slave_mon_proxy_h = this;
endfunction : end_of_elaboration_phase

//--------------------------------------------------------------------------------------------
// Task: run_phase
//  This task calls the monitor logic written in the monitor BFM at HDL side
//  Receives data packet from slave monitor bfm and converts into the transaction objects
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
task ahb_slave_monitor_proxy::run_phase(uvm_phase phase);
  AhbSlaveTransaction ahb_slave_packet;

  `uvm_info(get_type_name(), $sformatf("Inside the slave_monitor_proxy"), UVM_LOW);
  ahb_slave_packet = AhbSlaveTransaction::type_id::create("slave_packet");
  
  ahb_slave_mon_bfm_h.wait_for_hreset_n();

  forever begin
    ahb_transfer_char_s struct_data_packet;
    ahb_transfer_cfg_s  struct_cfg_packet; 
    AhbSlaveTransaction  ahb_slave_clone_packet;
    
    AhbSlaveConfigConverter.sv :: from_class (ahb_slave_agent_cfg_h, struct_cfg_packet);
    ahb_slave_mon_bfm_h.sample_data (struct_data_packet, struct_cfg_packet);
    AhbSlaveSequenceItemConverter :: to_class (struct_data_packet, ahb_slave_packet);

    `uvm_info(get_type_name(),$sformatf("Received packet from slave monitor bfm: , \n %s", ahb_slave_packet.sprint()),UVM_HIGH)

    //Clone and publish the cloned item to the subscribers
    $cast(ahb_slave_clone_packet, ahb_slave_packet.clone());
    `uvm_info(get_type_name(),$sformatf("Sending packet via analysis_port: , \n %s", ahb_slave_clone_packet.sprint()),UVM_HIGH)
    ahb_slave_analysis_port.write(ahb_slave_clone_packet);
  end

endtask : run_phase

`endif
