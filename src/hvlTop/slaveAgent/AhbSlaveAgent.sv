`ifndef AHBSLAVEAGENT_INCLUDED_
`define AHBSLAVEAGENT_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbSlaveAgent 
//  This agent is a configurable with respect to configuration which can create active and passive components
//  It contains testbench components like AhbSlaveSequencer,AhbSlaveDriverProxy and AhbSlaveMonitorProxy for AHB
//------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
class AhbSlaveAgent extends uvm_agent;
  `uvm_component_utils( AhbSlaveAgent)

  //Variable: ahbSlaveAgentConfig
  //Declaring handle for AhbSlaveAgentConfig class 
  AhbSlaveAgentConfig ahbSlaveAgentConfig;

  //Varible: ahbSlaveSequencer
  //Handle for  AhbSlaveSequencer
  AhbSlaveSequencer ahbSlaveSequencer;
  
  //Variable: ahbSlaveDriverProxy
  //Creating a Handle for AhbSlaveDriverProxy
  AhbSlaveDriverProxy ahbSlaveDriverProxy;

  //Variable: ahbSlaveMonitorProxy
  //Declaring a handle for AhbSlaveMonitorProxy
  AhbSlaveMonitorProxy ahbSlaveMonitorProxy;

  // Variable: ahbSlaveCoverage
  // Decalring a handle for AhbSlaveCoverage
  AhbSlaveCoverage ahbSlaveCoverage;
  
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
    function AhbSlaveAgent::new(string name = "AhbSlaveAgent",uvm_component parent = null);
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
    ahbSlaveSequencer = AhbSlaveSequencer::type_id::create("ahbSlaveSequencer",this);
    ahbSlaveDriverProxy = AhbSlaveDriverProxy::type_id::create("ahbSlaveDriverProxy",this);
  end

  ahbSlaveMonitorProxy = AhbSlaveMonitorProxy::type_id::create("ahbSlaveMonitorProxy",this);

  if(ahbSlaveAgentConfig.hasCoverage) begin
    ahbSlaveCoverage = AhbSlaveCoverage::type_id::create("ahbSlaveCoverage",this);
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
    ahbSlaveDriverProxy.ahbSlaveAgentConfig = ahbSlaveAgentConfig;
    ahbSlaveSequencer.ahbSlaveAgentConfig = ahbSlaveAgentConfig;
    
    //Connecting AhbSlaveDriverProxy port to AhbSlaveSequencer export
    ahbSlaveDriverProxy.seq_item_port.connect(ahbSlaveSequencer.seq_item_export);
  end
  ahbSlaveMonitorProxy.ahbSlaveAgentConfig = ahbSlaveAgentConfig;

  if(ahbSlaveAgentConfig.hasCoverage) begin
    ahbSlaveCoverage.ahbSlaveAgentConfig = ahbSlaveAgentConfig;
  
    //Connecting AhbSlaveMonitorProxyport to AhbSlaveCoverage export
    ahbSlaveMonitorProxy.ahbSlaveAnalysisPort.connect(ahbSlaveCoverage.analysis_export);
  end
    ahbSlaveMonitorProxy.ahbSlaveAgentConfig = ahbSlaveAgentConfig;

endfunction : connect_phase

`endif
