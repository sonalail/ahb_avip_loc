`ifndef AHBSLAVEBASESEQUENCE_INCLUDED_
`define AHBSLAVEBASESEQUENCE_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbSlaveBaseSequence
// Base sequence for the AHB slave. Provides the foundation for all AHB slave sequences.
//--------------------------------------------------------------------------------------------
class AhbSlaveBaseSequence extends uvm_sequence#(uvm_sequence_item);
  `uvm_object_utils(AhbSlaveBaseSequence)

  // Variable: seqr
  // Handle for the AHB slave sequencer
  AhbSlaveSequencer ahbSlaveSequencer;

  // Variable: item
  // Handle for the AHB slave transaction (sequence item)
  AhbSlaveTransaction ahbSlaveTransaction;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbSlaveBaseSequence");
  extern task body();
  
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

task AhbSlaveBaseSequence::body();

  //dynamic casting of p_sequencer and m_sequencer
  if(!$cast(p_sequencer,m_sequencer))begin
    `uvm_error(get_full_name(),"Virtual sequencer pointer cast failed")
  end
            
endtask : body


`endif
//------------------------------------------------------------------------------------------------






