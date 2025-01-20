`ifndef AHB_ENV_INCLUDED_
`define AHB_ENV_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbEnvironment
// Creates master agent and slave agent and scoreboard
//--------------------------------------------------------------------------------------------
class AhbEnvironment extends uvm_env;
  `uvm_component_utils(AhbEnvironment)

  //Variable: ahb_master_agent_h
  //Declaring ahb master agent handle
  AhbMasterAgent ahb_master_agent_h;

  //Variable: ahb_slave_agent_h
  //Declaring ahb slave agent handle
  AhbSlaveAgent  ahb_slave_agent_h;

  //Variable: ahb_scoreboard_h
  //Declaring ahb scoreboard handle
  AhbScoreboard ahb_scoreboard_h;

  //Variable: ahb_virtual_seqr_h
  //Declaring ahb virtual seqr handle
  AhbVirtualSequencer ahb_virtual_seqr_h;
  
  //Variable: ahb_env_cfg_h
  //Declaring handle for ahb_env_config_object
  AhbEnvironmentConfig ahb_env_cfg_h;  
  
  //Variable: ahb_slave_agent_cfg_h;
  //Handle for ahb_slave agent configuration
  AhbSlaveAgentConfig ahb_slave_agent_cfg_h;

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
  if(!uvm_config_db #(AhbEnvironmentConfig)::get(this,"","ahb_env_config",ahb_env_cfg_h)) begin
   `uvm_fatal("FATAL_ENV_CONFIG", $sformatf("Couldn't get the env_config from config_db"))
  end
  ahb_slave_agent_cfg_h = new[ahb_env_cfg_h.no_of_slaves];
  

  if(!uvm_config_db #( AhbSlaveAgentConfig)::get(this,"","ahb_slave_agent_config",ahb_slave_agent_cfg_h)) begin
    `uvm_fatal("FATAL_SA_AGENT_CONFIG", $sformatf("Couldn't get the ahb_slave_agent_config from config_db"))
    end
 
  
  ahb_master_agent_h = AhbMasterAgent::type_id::create("ahb_master_agent",this);
  
  ahb_slave_agent_h = new[ahb_env_cfg_h.no_of_slaves];

  ahb_slave_agent_h = AhbSlaveAgent ::type_id::create("ahb_slave_agent_h",this);
 

  if(ahb_env_cfg_h.has_virtual_seqr) begin
    ahb_virtual_seqr_h = AhbVirtualSequencer::type_id::create("ahb_virtual_seqr_h",this);
  end

  if(ahb_env_cfg_h.has_scoreboard) begin
    ahb_scoreboard_h = AhbScoreboard::type_id::create("ahb_scoreboard_h",this);
  end

  
    ahb_slave_agent_h.ahb_slave_agent_cfg_h = ahb_slave_agent_cfg_h;
  

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
  if(ahb_env_cfg_h.has_virtual_seqr) begin
    ahb_virtual_seqr_h.ahb_master_seqr_h = ahb_master_agent_h.ahb_master_seqr_h;
    ahb_virtual_seqr_h.ahb_slave_seqr_h = ahb_slave_agent_h.ahb_slave_seqr_h;
    end
  
  
  ahb_master_agent_h.ahb_master_mon_proxy_h.ahb_master_analysis_port.connect(ahb_scoreboard_h
                                                                    .ahb_master_analysis_fifo.analysis_export);
  
  ahb_slave_agent_h.ahb_slave_mon_proxy_h.ahb_slave_analysis_port.connect(ahb_scoreboard_h
                                                                      .ahb_slave_analysis_fifo.analysis_export);
  
  
endfunction : connect_phase

`endif
