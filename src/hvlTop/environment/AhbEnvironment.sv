`ifndef AHBENVIRONMENT_INCLUDED_
`define AHBENVIRONMENT_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbEnvironment
// Creates master agent and slave agent and scoreboard
//--------------------------------------------------------------------------------------------
class AhbEnvironment extends uvm_env;
  `uvm_component_utils(AhbEnvironment)

  //Variable: ahbMasterAgent
  //Declaring ahb master agent handle
  AhbMasterAgent ahbMasterAgent;

  //Variable: ahbSlaveAgent
  //Declaring ahb slave agent handle
  AhbSlaveAgent  ahbSlaveAgent;

  //Variable: ahbScoreboard
  //Declaring ahb scoreboard handle
  AhbScoreboard ahbScoreboard;

  //Variable: ahbVirtualSequencer
  //Declaring ahb virtual seqr handle
  AhbVirtualSequencer ahbVirtualSequencer;
  
  //Variable: ahbEnvironmentConfig
  //Declaring handle for ahb_env_config_object
  AhbEnvironmentConfig ahbEnvironmentConfig[];  
  
  //Variable: ahbSlaveAgentConfig;
  //Handle for ahb_slave agent configuration
  AhbSlaveAgentConfig ahbSlaveAgentConfig[];

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbEnvironment", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);

endclass : AhbEnvironment

//--------------------------------------------------------------------------------------------
// Construct: new
//
// Parameters:
//  name - AhbEnvironment
//  parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function AhbEnvironment::new(string name = "AhbEnvironment",uvm_component parent = null);
  super.new(name, parent);
endfunction : new

//--------------------------------------------------------------------------------------------
// Function: build_phase
// Builds the master and slave agents and scoreboard
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void AhbEnvironment::build_phase(uvm_phase phase);
  super.build_phase(phase);
  if(!uvm_config_db #(AhbEnvironmentConfig)::get(this,"","AhbEnvironmentConfig",ahbEnvironmentConfig)) begin
   `uvm_fatal("FATAL_ENV_CONFIG", $sformatf("Couldn't get the ahbEnvironmentConfig from config_db"))
  end
  ahbSlaveAgentConfig= new[ahbEnvironmentConfig.noOfSlaves];
  

  if(!uvm_config_db #(AhbSlaveAgentConfig)::get(this,"","AhbSlaveAgentConfig",ahbSlaveAgentConfig)) begin
    `uvm_fatal("FATAL_SA_AGENT_CONFIG", $sformatf("Couldn't get the ahbSlaveAgentConfig from config_db"))
    end
 
  
  ahbMasterAgent = AhbMasterAgent::type_id::create("ahbMasterAgent",this);
  
  ahbSlaveAgent = new[ahbEnvironmentConfig.noOfSlaves];

  ahbSlaveAgent = AhbSlaveAgent::type_id::create("ahbSlaveAgent",this);
 

  if(ahbEnvironmentConfig.hasVirtualSequencer) begin
    ahbVirtualSequencer = AhbVirtualSequencer::type_id::create("ahbVirtualSequencer",this);
  end

  if(ahbEnvironmentConfig.hasScoreboard) begin
    ahbScoreboard = AhbScoreboard::type_id::create("ahbScoreboard",this);
  end

  
    ahbSlaveAgent.ahbSlaveAgentConfig = ahbSlaveAgentConfig;
  

endfunction : build_phase

//--------------------------------------------------------------------------------------------
// Function: connect_phase
//  Connects the master agent monitor's analysis_port with scoreboard's analysis_fifo 
//  Connects the slave agent monitor's analysis_port with scoreboard's analysis_fifo 
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void AhbEnvironment::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  if(ahbEnvironmentConfig.hasVirtualSequencer) begin
    ahbVirtualSequencer.ahbMasterSequencer = ahbMasterAgent.ahbMasterSequencer;
    ahbVirtualSequencer.ahbSlaveSequencer = ahbSlaveAgent.ahbSlaveSequencer;
    end
  
  
  ahbMasterAgent.ahbMasterMonitorProxy.ahbMasterAnalysisPort.connect(ahbScoreboard.ahbMasterAnalysisFifo.analysisExport);
  
  ahbSlaveAgent.ahbSlaveMonitorProxy.ahbSlaveAnalysisPort.connect(ahbScoreboard.ahbSlaveAnalysisFifo.analysisExport);
  
  
endfunction : connect_phase

`endif
