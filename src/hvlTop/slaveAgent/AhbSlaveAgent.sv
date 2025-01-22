`ifndef AHBSLAVEAGENT_INCLUDED_
`define AHBSLAVEAGENT_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbSlaveAgent 
//  This agent is a configurable with respect to configuration which can create active and passive components
//  It contains testbench components like AhbSlaveSequencer,AhbSlaveDriverProxy and AhbSlaveMonitorProxy for AHB
//------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
class AhbSlaveAgent extends uvm_agent;
  `uvm_component_utils( AhbSlaveAgent)

  //Variable: ahb_slave_agent_cfg_h
  //Declaring handle for AhbSlaveAgentConfig class 
  AhbSlaveAgentConfig ahbSlaveAgentConfig;

  //Varible: ahbSlaveSeqr
  //Handle for  AhbSlaveSequencer
  AhbSlaveSequencer ahbSlaveSeqr;
  
  //Variable: ahbSlaveDrvProxy
  //Creating a Handle for AhbSlaveDriverProxy
  AhbSlaveDriverProxy ahbSlaveDrvProxy;

  //Variable: apbSlaveMonProxy
  //Declaring a handle for AhbSlaveMonitorProxy
  AhbSlaveMonitorProxy ahbSlaveMonProxy;

  // Variable: ahbSlaveCov
  // Decalring a handle for AhbSlaveCoverage
  AhbSlaveCoverage ahbSlaveCov;
  
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

  if(!uvm_config_db #(AhbSlaveAgentConfig)::get(this,"","AhbSlaveAgentConfig", ahbSlaveAgentConfig)) begin
    `uvm_fatal("FATAL_MA_CANNOT_GET_AHB_SLAVE_AGENT_CONFIG", "cannot get ahbMasterAgentConfig from uvm_config_db");
  end

  if(ahbSlaveAgentConfig.is_active == UVM_ACTIVE) begin
    
    
    ahbSlaveSeqr = AhbSlaveSequencer::type_id::create("ahbSlaveSeqr",this);
    ahbSlaveDrvProxy = AhbSlaveDriverProxy::type_id::create("ahbSlaveDrvProxy",this);
  end

  ahbSlaveMonProxy=AhbSlaveMonitorProxy::type_id::create("ahbSlaveMonProxy",this);

  if(ahbSlaveAgentConfig.has_coverage) begin
    ahbSlaveCov = AhbSlaveCoverage::type_id::create("ahbSlaveCov",this);
  end

endfunction : build_phase

//--------------------------------------------------------------------------------------------
// Function: connect_phase 
// Connecting AhbSlaveDriver, AhbSlaveMonitor and AhbSlaveSequencer for configuration
//
// Parameters:
// phase - uvm phase
//--------------------------------------------------------------------------------------------
function void AhbSlaveAgent::connect_phase(uvm_phase phase);
  if(ahbSlaveAgentConfig.is_active == UVM_ACTIVE) begin
    ahbSlaveDrvProxy.ahbSlaveAgentConfig = ahbSlaveAgentConfig;
    ahbSlaveSeqr.ahbSlaveAgentConfig = ahbSlaveAgentConfig;
    
    //Connecting AhbSlaveDriverProxy port to AhbSlaveSequencer export
    ahbSlaveDrvProxy.seq_item_port.connect(ahbSlaveSeqr.seq_item_export);
  end
  ahbSlaveMonProxy.ahbSlaveAgentConfig = ahbSlaveAgentConfig;

  if(ahbSlaveAgentConfig.has_coverage) begin
    ahbSlaveCov.ahbSlaveAgentConfig = ahbSlaveAgentConfig;
  
    //Connecting AhbSlaveMonitorProxyport to AhbSlaveCoverage export
    ahbSlaveMonProxy.ahbSlaveAnalysisPort.connect(ahbSlaveCov.analysis_export);
  end
    ahbSlaveMonProxy.ahbSlaveAgentConfig = ahbSlaveAgentConfig;

endfunction : connect_phase

`endif
