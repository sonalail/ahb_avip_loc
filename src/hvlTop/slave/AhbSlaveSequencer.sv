`ifndef AHB_SLAVE_SEQUENCER_INCLUDED_
`define AHB_SLAVE_SEQUENCER_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbSlaveSequencer
//  It send transactions to driver via tlm ports
//--------------------------------------------------------------------------------------------
class AhbSlaveSequencer extends uvm_sequencer#(AhbSlaveTransaction);
  `uvm_component_utils(AhbSlaveSequencer)
  
  //Variable: ahb_slave_agent_cfg_h;
  //Handle for  ahb slave agent configuration
  ahb_slave_agent_config ahb_slave_agent_cfg_h;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbSlaveSequencer", uvm_component parent = null);
  
endclass : AhbSlaveSequencer

//--------------------------------------------------------------------------------------------
// Construct: new
//  AhbSlaveSequencer class object is initialized
//
// Parameters:
//  name - AhbSlaveSequencer
//  parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function AhbSlaveSequencer::new(string name = "AhbSlaveSequencer",uvm_component parent = null);
  super.new(name, parent);
endfunction : new

`endif
