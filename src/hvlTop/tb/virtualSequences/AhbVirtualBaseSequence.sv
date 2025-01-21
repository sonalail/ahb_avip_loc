`ifndef AHBVIRTUALBASESEQ_INCLUDED_
`define AHBVIRTUALBASESEQ_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbVirtualBaseSequence
// Holds the handle of actual sequencer.
//--------------------------------------------------------------------------------------------
class AhbVirtualBaseSequence extends uvm_sequence;
  `uvm_object_utils(AhbVirtualBaseSequence)
  
  //Declaring p_sequencer
  `uvm_declare_p_sequencer(AhbVirtualSequencer)
 
  //Variable : apbMasterSequencer
  //Declaring handle to the virtual sequencer
  ApbMasterSequencer apbMasterSequencer;
 
  //Variable : apbMasterSequencer
  //Declaring handle to the virtual sequencer
  ApbSlaveSequencer apbSlaveSequencer;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbVirtualBaseSequence");
  extern task body();

endclass : AhbVirtualBaseSequence

//--------------------------------------------------------------------------------------------
// Construct: new
//
// Parameters:
//  name - AhbVirtualBaseSequence
//--------------------------------------------------------------------------------------------
function AhbVirtualBaseSequence::new(string name = "AhbVirtualBaseSequence");
  super.new(name);
endfunction : new

//--------------------------------------------------------------------------------------------
// Task : body
// Used to connect the master virtual seqr to master seqr
//
// Parameters:
//  name - AhbVirtualBaseSequence
//--------------------------------------------------------------------------------------------
task AhbVirtualBaseSequence::body();
  if(!$cast(p_sequencer,m_sequencer))begin
    `uvm_error(get_full_name(),"Virtual sequencer pointer cast failed")
  end
  apbSlaveSequencer  = p_sequencer.apbSlaveSequencer;
  apbMasterSequencer = p_sequencer.apbMasterSequencer;

endtask : body

`endif
