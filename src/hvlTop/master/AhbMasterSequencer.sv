<<<<<<< HEAD
`ifndef AHB_MASTER_SEQUENCER_INCLUDED_
`define AHB_MASTER_SEQUENCER_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbMasterSequencer
//--------------------------------------------------------------------------------------------
class AhbMasterSequencer extends uvm_sequencer #(AhbMasterTransaction);
  `uvm_component_utils(AhbMasterSequencer)

  //Variable: ahb_master_agent_cfg_h
  //Declaring handle for AhbMasterAgentConfig class 
  AhbMasterAgentConfig ahb_master_agent_cfg_h;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbMasterSequencer", uvm_component parent);
    
endclass : AhbMasterSequencer
 
//--------------------------------------------------------------------------------------------
// Construct: new
//  Initializes the AhbMasterSequencer class component
//
// Parameters:
//  name - AhbMasterSequencer
//  parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function AhbMasterSequencer::new(string name = "AhbMasterSequencer",uvm_component parent);
  super.new(name,parent);
endfunction : new

`endif

=======
`ifndef AHB_MASTER_SEQUENCER_INCLUDED_
`define AHB_MASTER_SEQUENCER_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbMasterSequencer
//--------------------------------------------------------------------------------------------
class AhbMasterSequencer extends uvm_sequencer #(AhbMasterTransaction);
  `uvm_component_utils(AhbMasterSequencer)

  //Variable: ahb_master_agent_cfg_h
  //Declaring handle for AhbMasterAgentConfig class 
  AhbMasterAgentConfig ahb_master_agent_cfg_h;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbMasterSequencer", uvm_component parent);
    
endclass : AhbMasterSequencer
 
//--------------------------------------------------------------------------------------------
// Construct: new
//  Initializes the AhbMasterSequencer class component
//
// Parameters:
//  name - AhbMasterSequencer
//  parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function AhbMasterSequencer::new(string name = "AhbMasterSequencer",uvm_component parent);
  super.new(name,parent);
endfunction : new

`endif
>>>>>>> c4a41554dec648b589a48044bdf6bc69b7934a01
