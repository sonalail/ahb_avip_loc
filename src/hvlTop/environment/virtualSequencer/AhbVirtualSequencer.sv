`ifndef AHBVIRTUALSEQUENCER_INCLUDED_
`define AHBVIRTUALSEQUENCER_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbVirtualSequencer
// Contains handles for AHB master and slave virtual sequencers
//--------------------------------------------------------------------------------------------
class AhbVirtualSequencer extends uvm_sequencer#(uvm_sequence_item);
  `uvm_component_utils(AhbVirtualSequencer)

  // Variable: ahbMasterVirtualSequencer
  // Declaring master virtual sequencer handle
  AhbMasterVirtualSequencer ahbMasterVirtualSequencer;

  // Variable: ahbSlaveVirtualSequencer
  // Declaring slave virtual sequencer handle
  AhbSlaveVirtualSequencer ahbSlaveVirtualSequencer;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbVirtualSequencer", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual function void start_of_simulation_phase (uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
    
endclass : AhbVirtualSequencer

//--------------------------------------------------------------------------------------------
// Construct: new
// Initializes the virtual sequencer
//
// Parameters:
//  name - AhbVirtualSequencer
//  parent - Parent under which this component is created
//--------------------------------------------------------------------------------------------
function AhbVirtualSequencer::new(string name = "AhbVirtualSequencer",
                                    uvm_component parent = null);
  super.new(name, parent);
endfunction : new

//--------------------------------------------------------------------------------------------
// Function: build_phase
// Creates and initializes virtual sequencer components
//
// Parameters:
//  phase - UVM phase
//--------------------------------------------------------------------------------------------
function void AhbVirtualSequencer::build_phase(uvm_phase phase);
  super.build_phase(phase);
endfunction : build_phase

//--------------------------------------------------------------------------------------------
// Function: connect_phase
// Establishes connections between components
//
// Parameters:
//  phase - UVM phase
//--------------------------------------------------------------------------------------------
function void AhbVirtualSequencer::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
endfunction : connect_phase
//---------------------------------------------------------------------------------------------

//--------------------------------------------------------------------------------------------
// Function: end_of_elaboration_phase
// <Description_here>
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void AhbVirtualSequencer::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);
endfunction  : end_of_elaboration_phase

//--------------------------------------------------------------------------------------------
// Function: start_of_simulation_phase
// <Description_here>
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void AhbVirtualSequencer::start_of_simulation_phase(uvm_phase phase);
  super.start_of_simulation_phase(phase);
endfunction : start_of_simulation_phase

//--------------------------------------------------------------------------------------------
// Task: run_phase
// <Description_here>
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
task AhbVirtualSequencer::run_phase(uvm_phase phase);

  // Work here
  `uvm_info("virtual sequencer","virtual sequencer",UVM_LOW)
  // ...

endtask : run_phase

`endif
// ------------------------------------------------------------------------------------------------
