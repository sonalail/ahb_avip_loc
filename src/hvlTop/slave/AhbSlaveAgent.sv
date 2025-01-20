`ifndef AHB_SLAVE_AGENT_INCLUDED_
`define AHB_SLAVE_AGENT_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbSlaveAgent 
//  This agent is a configurable with respect to configuration which can create active and passive components
//  It contains testbench components like AhbSlaveSequencer,AhbSlaveDriverProxy and AhbSlaveMonitorProxy for AHB
//------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
class AhbSlaveAgent extends uvm_agent;
  `uvm_component_utils( AhbSlaveAgent)

  //Variable: ahb_slave_agent_cfg_h
  //Declaring handle for AhbSlaveAgentConfig class 
  AhbSlaveAgentConfig ahb_slave_agent_cfg_h;

  //Varible: ahb_slave_seqr_h
  //Handle for  AhbSlaveSequencer
  AhbSlaveSequencer ahb_slave_seqr_h;
  
  //Variable: ahb_slave_drv_proxy_h
  //Creating a Handle for AhbSlaveDriverProxy
  AhbSlaveDriverProxy ahb_slave_drv_proxy_h;

  //Variable: apb_slave_mon_proxy_h
  //Declaring a handle for AhbSlaveMonitorProxy
  AhbSlaveMonitorProxy ahb_slave_mon_proxy_h;

  // Variable: ahb_slave_cov_h
  // Decalring a handle for AhbSlaveCoverage
  AhbSlaveCoverage ahb_slave_cov_h;

  // Variable: ahb_reg_adapter_h
  // Declaring a handle for AhbSlaveAdapter
  AhbSlaveAdapter ahb_reg_adapter_h;
    
  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbSlaveAgent", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
 
    
endclass :AhbSlaveAgent
 //-----------------------------------------------------------------------------
// Construct: new
//  Initializes memory for new object
//
// Parameters:
//  name - instance name of the AhbSlaveAgent
//  parent - parent under which this component is created
//-------------------------------------------------------------------------
    function AhbSlaveAgent::new(string name = "AhbSlaveAgent",
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
function void AhbSlaveAgent::build_phase(uvm_phase phase);
  super.build_phase(phase);

  if(!uvm_config_db #(AhbSlaveAgentConfig)::get(this,"","AhbSlaveAgentConfig", ahb_slave_agent_cfg_h)) begin
    `uvm_fatal("FATAL_MA_CANNOT_GET_AHB_SLAVE_AGENT_CONFIG", "cannot get ahb_master_agent_cfg_h from uvm_config_db");
  end

  if(ahb_slave_agent_cfg_h.is_active == UVM_ACTIVE) begin
    
    
    ahb_slave_seqr_h=AhbSlaveSequencer::type_id::create("ahb_slave_seqr_h",this);
    ahb_slave_drv_proxy_h=AhbSlaveDriverProxy::type_id::create("ahb_slave_drv_proxy_h",this);
  end

  ahb_slave_mon_proxy_h=AhbSlaveMonitorProxy::type_id::create("ahb_slave_mon_proxy_h",this);

  if(ahb_slave_agent_cfg_h.has_coverage) begin
    ahb_slave_cov_h = AhbSlaveCoverage::type_id::create("ahb_slave_cov_h",this);
  end

  ahb_reg_adapter_h = AhbSlaveAdapter::type_id::create("ahb_reg_adapter_h"); 
endfunction : build_phase

//--------------------------------------------------------------------------------------------
// Function: connect_phase 
// Connecting AhbSlaveDriver, AhbSlaveMonitor and AhbSlaveSequencer for configuration
//
// Parameters:
// phase - uvm phase
//--------------------------------------------------------------------------------------------
function void AhbSlaveAgent::connect_phase(uvm_phase phase);
  if(ahb_slave_agent_cfg_h.is_active == UVM_ACTIVE) begin
    ahb_slave_drv_proxy_h.ahb_slave_agent_cfg_h = ahb_slave_agent_cfg_h;
    ahb_slave_seqr_h.ahb_slave_agent_cfg_h = ahb_slave_agent_cfg_h;
    
    //Connecting AhbSlaveDriverProxy port to AhbSlaveSequencer export
    ahb_slave_drv_proxy_h.seq_item_port.connect(ahb_slave_seqr_h.seq_item_export);
  end
  ahb_slave_mon_proxy_h.ahb_slave_agent_cfg_h = ahb_slave_agent_cfg_h;

  if(ahb_slave_agent_cfg_h.has_coverage) begin
    ahb_slave_cov_h.ahb_slave_agent_cfg_h = ahb_slave_agent_cfg_h;
  
    //Connecting AhbSlaveMonitorProxyport to AhbSlaveCoverage export
    ahb_slave_mon_proxy_h.ahb_slave_analysis_port.connect(ahb_slave_cov_h.analysis_export);
  end
    ahb_slave_mon_proxy_h.ahb_slave_agent_cfg_h = ahb_slave_agent_cfg_h;

endfunction : connect_phase

`endif
