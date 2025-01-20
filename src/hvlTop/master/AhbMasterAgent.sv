`ifndef AHB_MASTER_AGENT_INCLUDED_
`define AHB_MASTER_AGENT_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbMasterAgent 
//  This agent is a configurable with respect to configuration which can create active and passive components
//  It contains testbench components like AhbMasterSequencer,AhbMasterDriverProxy and AhbMasterMonitorProxy for AHB
//------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
class AhbMasterAgent extends uvm_agent;
  `uvm_component_utils(AhbMasterAgent)

  //Variable: ahb_master_agent_cfg_h
  //Declaring handle for AhbMasterAgentConfig class 
  AhbMasterAgentConfig ahb_master_agent_cfg_h;

  //Varible: ahb_master_seqr_h
  //Handle for  AhbMasterSequencer
  AhbMasterSequencer ahb_master_seqr_h;
  
  //Variable: ahb_master_drv_proxy_h
  //Creating a Handle for AhbMasterDriverProxy
  AhbMasterDriverProxy ahb_master_drv_proxy_h;

  //Variable: apb_master_mon_proxy_h
  //Declaring a handle for AhbMasterMonitorProxy
  AhbMasterMonitorProxy ahb_master_mon_proxy_h;

  // Variable: ahb_master_cov_h
  // Decalring a handle for AhbMasterCoverage
  AhbMasterCoverage ahb_master_cov_h;

  // Variable: ahb_reg_adapter_h
  // Declaring a handle for AhbMasterAdapter
  AhbMasterAdapter ahb_reg_adapter_h;
    
  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbMasterAgent", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
 
    
endclass :AhbMasterAgent
 //-----------------------------------------------------------------------------
// Construct: new
//  Initializes memory for new object
//
// Parameters:
//  name - instance name of the AhbMasterAgent
//  parent - parent under which this component is created
//-------------------------------------------------------------------------
function AhbMasterAgent::new(string name = "AhbMasterAgent",
                                    uvm_component parent = null);
  super.new(name, parent);
endfunction : new
    
 //--------------------------------------------------------------------------------------------
// Function: build_phase
// Creates the required ports, gets the required configuration from confif_db
//
// Parameters:
// phase - uvm phase
//--------------------------------------------------------------------------------------------
function void AhbMasterAgent::build_phase(uvm_phase phase);
  super.build_phase(phase);

  if(!uvm_config_db #(AhbMasterAgentConfig)::get(this,"","AhbMasterAgentConfig", ahb_master_agent_cfg_h)) begin
    `uvm_fatal("FATAL_MA_CANNOT_GET_AHB_MASTER_AGENT_CONFIG", "cannot get ahb_master_agent_cfg_h from uvm_config_db");
  end

  if(ahb_master_agent_cfg_h.is_active == UVM_ACTIVE) begin
    
    
    ahb_master_seqr_h=AhbMasterSequencer::type_id::create("ahb_master_seqr_h",this);
        ahb_master_drv_proxy_h=AhbMasterDriverProxy::type_id::create("ahb_master_drv_proxy_h",this);
  end

  ahb_master_mon_proxy_h=AhbMasterMonitorProxy::type_id::create("ahb_master_mon_proxy_h",this);

  if(ahb_master_agent_cfg_h.has_coverage) begin
    ahb_master_cov_h = AhbMasterCoverage::type_id::create("ahb_master_cov_h",this);
  end

  ahb_reg_adapter_h = AhbMasterAdapter::type_id::create("ahb_reg_adapter_h"); 
endfunction : build_phase

//--------------------------------------------------------------------------------------------
// Function: connect_phase 
// Connecting AhbMasterDriver, AhbMasterMonitor and AhbMasterSequencer for configuration
//
// Parameters:
// phase - uvm phase
//--------------------------------------------------------------------------------------------
function void AhbMasterAgent::connect_phase(uvm_phase phase);
  if(ahb_master_agent_cfg_h.is_active == UVM_ACTIVE) begin
    ahb_master_drv_proxy_h.ahb_master_agent_cfg_h = ahb_master_agent_cfg_h;
    ahb_master_seqr_h.ahb_master_agent_cfg_h = ahb_master_agent_cfg_h;
    
    //Connecting driver_proxy port to sequencer export
    ahb_master_drv_proxy_h.seq_item_port.connect(ahb_master_seqr_h.seq_item_export);
  end
  ahb_master_mon_proxy_h.ahb_master_agent_cfg_h = ahb_master_agent_cfg_h;

  if(ahb_master_agent_cfg_h.has_coverage) begin
    ahb_master_cov_h.ahb_master_agent_cfg_h = ahb_master_agent_cfg_h;
  
    //Connecting monitor_proxy port to coverage export
    ahb_master_mon_proxy_h.ahb_master_analysis_port.connect(ahb_master_cov_h.analysis_export);
  end
    ahb_master_mon_proxy_h.ahb_master_agent_cfg_h = ahb_master_agent_cfg_h;

endfunction : connect_phase

`endif
