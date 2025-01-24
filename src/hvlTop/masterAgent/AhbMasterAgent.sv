`ifndef AHBMASTERAGENT_INCLUDED_
`define AHBMASTERAGENT_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbMasterAgent 
//  This agent is a configurable with respect to configuration which can create active and passive components
//  It contains testbench components like AhbMasterSequencer,AhbMasterDriverProxy and AhbMasterMonitorProxy for AHB
//------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
class AhbMasterAgent extends uvm_agent;
  `uvm_component_utils(AhbMasterAgent)

  //Variable: ahbMasterAgentConfig
  //Declaring handle for AhbMasterAgentConfig class 
  AhbMasterAgentConfig ahbMasterAgentConfig;

  //Varible: ahbMasterSequencer
  //Handle for  AhbMasterSequencer
  AhbMasterSequencer ahbMasterSequencer;
  
  //Variable: ahbMasterDriverProxy
  //Creating a Handle for AhbMasterDriverProxy
  AhbMasterDriverProxy ahbMasterDriverProxy;

  //Variable: ahbMasterMonitorProxy
  //Declaring a handle for AhbMasterMonitorProxy
  AhbMasterMonitorProxy ahbMasterMonitorProxy;

  // Variable: ahbMasterCoverage
  // Decalring a handle for AhbMasterCoverage
  AhbMasterCoverage ahbMasterCoverage;
    
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
function AhbMasterAgent::new(string name = "AhbMasterAgent",uvm_component parent = null);
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

  if(!uvm_config_db #(AhbMasterAgentConfig)::get(this,"","AhbMasterAgentConfig", ahbMasterAgentConfig)) begin
    `uvm_error("FATAL MASTER CANNOT GET AHBMASTERAGENTCONFIG", "cannot get ahbMasterAgentConfig from uvm_config_db");
  end

  if(ahbMasterAgentConfig.is_active == UVM_ACTIVE) begin
        ahbMasterSequencer = AhbMasterSequencer::type_id::create("ahbMasterSequencer",this);
        ahbMasterDriverProxy = AhbMasterDriverProxy::type_id::create("ahbMasterDriverProxy",this);
  end
  
  ahbMasterMonitorProxy = AhbMasterMonitorProxy::type_id::create("ahbMasterMonitorProxy",this);

  if(ahbMasterAgentConfig.hasCoverage) begin
    ahbMasterCoverage = AhbMasterCoverage::type_id::create("ahbMasterCoverage",this);
  end
  
endfunction : build_phase

//--------------------------------------------------------------------------------------------
// Function: connect_phase 
// Connecting AhbMasterDriver, AhbMasterMonitor and AhbMasterSequencer for configuration
//
// Parameters:
// phase - uvm phase
//--------------------------------------------------------------------------------------------
function void AhbMasterAgent::connect_phase(uvm_phase phase);
  if(ahbMasterAgentConfig.is_active == UVM_ACTIVE) begin
    ahbMasterDriverProxy.ahbMasterAgentConfig = ahbMasterAgentConfig;
    ahbMasterSequencer.ahbMasterAgentConfig = ahbMasterAgentConfig;
    
    //Connecting AhbSlaveDriverProxy port to AhbSlaveSequencer export
    ahbMasterDriverProxy.seq_item_port.connect(ahbMasterSequencer.seq_item_export);
  end
  ahbMasterMonitorProxy.ahbMasterAgentConfig = ahbMasterAgentConfig;

  if(ahbMasterAgentConfig.hasCoverage) begin
    ahbMasterCoverage.ahbMasterAgentConfig = ahbMasterAgentConfig;
  
    //Connecting AhbSlaveMonitorProxy port to AhbSlaveSequencerCoverage export
    ahbMasterMonitorProxy.ahbMasterAnalysisPort.connect(ahbMasterCoverage.analysis_export);
  end
    ahbMasterMonitorProxy.ahbMasterAgentConfig = ahbMasterAgentConfig;

endfunction : connect_phase

`endif
