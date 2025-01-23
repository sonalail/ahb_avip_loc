`ifndef AHBMASTERBASESEQUENCE_INCLUDED_
`define AHBMASTERBASESEQUENCE_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbMasterBaseSequence
// Base sequence for the AHB master. Provides the foundation for all AHB master sequences.
//--------------------------------------------------------------------------------------------
class AhbMasterBaseSequence extends uvm_sequence#(uvm_sequence_item);
  `uvm_object_utils(AhbMasterBaseSequence)

  // Variable: ahbMasterSequencer
  // Handle for the AHB master sequencer
  AhbMasterSequencer ahbMasterSequencer;

  // Variable: ahbMasterTransaction
  // Handle for the AHB master transaction (sequence item)
  AhbMasterTransaction ahbMasterTransaction;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbMasterBaseSequence");
  extern task body();  
  
endclass : AhbMasterBaseSequence

//--------------------------------------------------------------------------------------------
// Construct: new
// Initializes the base sequence
//
// Parameters:
//  name - Name of the sequence
//--------------------------------------------------------------------------------------------
function AhbMasterBaseSequence::new(string name = "AhbMasterBaseSequence");
  super.new(name);
endfunction : new

task AhbMasterBaseSequence::body();

  //dynamic casting of p_sequencer and m_sequencer
  if(!$cast(p_sequencer,m_sequencer))begin
    `uvm_error(get_full_name(),"Virtual sequencer pointer cast failed")
  end
            
endtask : body
`endif
//------------------------------------------------------------------------------------------------






