`ifndef AHB_SLAVE_BASE_SEQUENCE_INCLUDED_
`define AHB_SLAVE_BASE_SEQUENCE_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbSlaveBaseSequence
// Base sequence for the AHB slave. Provides the foundation for all AHB slave sequences.
//--------------------------------------------------------------------------------------------
class AhbSlaveBaseSequence extends uvm_sequence#(uvm_sequence_item);
  `uvm_object_utils(AhbSlaveBaseSequence)

  // Variable: seqr_h
  // Handle for the AHB slave sequencer
  AhbSlaveSequencer ahb_slave_seqr_h;

  // Variable: item_h
  // Handle for the AHB slave transaction (sequence item)
  AhbSlaveTransaction ahb_slave_tx_h;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbSlaveBaseSequence");
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual function void start_of_simulation_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);

endclass : AhbSlaveBaseSequence

//--------------------------------------------------------------------------------------------
// Construct: new
// Initializes the base sequence
//
// Parameters:
//  name - Name of the sequence
//--------------------------------------------------------------------------------------------
function AhbSlaveBaseSequence::new(string name = "AhbSlaveBaseSequence");
  super.new(name);
endfunction : new

//--------------------------------------------------------------------------------------------
// Function: build_phase
// Called during the UVM build phase
//
// Parameters:
//  phase - UVM phase
//--------------------------------------------------------------------------------------------
function void AhbSlaveBaseSequence::build_phase(uvm_phase phase);
  super.build_phase(phase);
  // Add any initialization here, such as assigning sequencer handles
endfunction : build_phase

//--------------------------------------------------------------------------------------------
// Function: end_of_elaboration_phase
// Called at the end of the elaboration phase
//
// Parameters:
//  phase - UVM phase
//--------------------------------------------------------------------------------------------
function void AhbSlaveBaseSequence::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);
  // Add actions to be performed at the end of elaboration
endfunction : end_of_elaboration_phase

//--------------------------------------------------------------------------------------------
// Function: start_of_simulation_phase
// Called during the start of simulation
//
// Parameters:
//  phase - UVM phase
//--------------------------------------------------------------------------------------------
function void AhbSlaveBaseSequence::start_of_simulation_phase(uvm_phase phase);
  super.start_of_simulation_phase(phase);
  // Add actions to be performed at simulation start
endfunction : start_of_simulation_phase

//--------------------------------------------------------------------------------------------
// Task: run_phase
// Main phase for the sequence
//
// Parameters:
//  phase - UVM phase
//--------------------------------------------------------------------------------------------
task AhbSlaveBaseSequence::run_phase(uvm_phase phase);
  `uvm_info("AHB_SLAVE_BASE_SEQUENCE", "AHB slave base sequence started", UVM_LOW)
  
 

  // Add sequence logic here
  // Example: Execute transactions 

  
endtask : run_phase

`endif
------------------------------------------------------------------------------------------------






