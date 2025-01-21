
`ifndef APB_MASTER_MONITOR_PROXY_INCLUDED_
`define APB_MASTER_MONITOR_PROXY_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbMasterMonitorProxy
//  This is the HVL side AhbMasterMonitorProxy
//  It gets the sampled data from the HDL master monitor and converts them into transaction items
//--------------------------------------------------------------------------------------------
class AhbMasterMonitorProxy extends uvm_monitor; 
  `uvm_component_utils(AhbMasterMonitorProxy)
  
  // Variable: ahb_master_mon_bfm_h
  // Declaring handle for ahb monitor bfm
  virtual AhbMasterMonitorBfm ahb_master_mon_bfm_h;
   
  // Variable: ahb_master_agent_cfg_h
  // Declaring handle for AhbMasterAgentConfig class 
  AhbMasterAgentConfig ahb_master_agent_cfg_h;
    
  // Variable: ahb_master_analysis_port
  // Declaring analysis port for the monitor port
  uvm_analysis_port#(AhbMasterTransaction) ahb_master_analysis_port;
  
  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbMasterMonitorProxy", uvm_component parent);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);

endclass : AhbMasterMonitorProxy

//--------------------------------------------------------------------------------------------
// Construct: new
//  Initializes memory for new object
//
// Parameters:
//  name   - AhbMasterMonitorProxy
//  parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function AhbMasterMonitorProxy::new(string name = "AhbMasterMonitorProxy",uvm_component parent);
  super.new(name, parent);
  ahb_master_analysis_port = new("ahb_master_analysis_port",this);
endfunction : new

//--------------------------------------------------------------------------------------------
// Function: build_phase
//  Creates the required ports, gets the required configuration from confif_db
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void AhbMasterMonitorProxy::build_phase(uvm_phase phase);
  super.build_phase(phase);
  if(!uvm_config_db #(virtual AhbMasterMonitorBfm)::get(this,"","AhbMasterMonitorBfm", ahb_master_mon_bfm_h)) begin
    `uvm_fatal("FATAL_MDP_CANNOT_GET_AHB_MASTER_MONITOR_BFM","cannot get() ahb_master_mon_bfm_h");
  end
endfunction : build_phase

//--------------------------------------------------------------------------------------------
// Function: end_of_elaboration_phase
//  Pointing handle of monitor proxy in HDL BFM to this proxy method in HVL part
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void AhbMasterMonitorProxy::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);
  ahb_master_mon_bfm_h.ahb_master_mon_proxy_h = this;
endfunction : end_of_elaboration_phase

//--------------------------------------------------------------------------------------------
// Task: run_phase
//  This task calls the monitor logic written in the monitor BFM at HDL side
//  Receives data packet from slave monitor bfm and converts into the transaction objects
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
task ahb_master_monitor_proxy::run_phase(uvm_phase phase);
  AhbMasterTransaction ahb_master_packet;

  `uvm_info(get_type_name(), $sformatf("Inside the master_monitor_proxy"), UVM_LOW);
  ahb_master_packet = AhbMasterTransaction::type_id::create("master_packet");
  
  ahb_master_mon_bfm_h.wait_for_HRESETn();

  forever begin
    ahb_transfer_char_s struct_data_packet;
    ahb_transfer_cfg_s  struct_cfg_packet; 
    AhbMasterTransaction  ahb_master_clone_packet;
    
    AhbMasterConfigConverter.sv :: from_class (ahb_master_agent_cfg_h, struct_cfg_packet);
    ahb_master_mon_bfm_h.sample_data (struct_data_packet, struct_cfg_packet);
    AhbMasterSequenceItemConverter :: to_class (struct_data_packet, ahb_master_packet);

    `uvm_info(get_type_name(),$sformatf("Received packet from master monitor bfm: , \n %s", ahb_master_packet.sprint()),UVM_HIGH)

    //Clone and publish the cloned item to the subscribers
    $cast(ahb_master_clone_packet, ahb_master_packet.clone());
    `uvm_info(get_type_name(),$sformatf("Sending packet via analysis_port: , \n %s", ahb_master_clone_packet.sprint()),UVM_HIGH)
    ahb_master_analysis_port.write(ahb_master_clone_packet);
  end

endtask : run_phase

`endif

