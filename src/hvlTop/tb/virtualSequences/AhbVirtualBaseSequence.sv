`ifndef AHBVIRTUALBASESEQUENCE_INCLUDED_
`define AHBVIRTUALBASESEQUENCE_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbVirtualBaseSequence
// Holds the handle of actual sequencer.
//--------------------------------------------------------------------------------------------
class AhbVirtualBaseSequence extends uvm_sequence#(uvm_seq_item); 
  `uvm_object_utils(AhbVirtualBaseSequence)
  
  //Declaring p_sequencer
  `uvm_declare_p_sequencer(AhbMasterSequencer);
  `uvm_declare_p_sequencer(AhbSlaveSequencer);
 
  //Variable : apbMasterSequencer
  //Declaring handle to the virtual sequencer
  AhbMasterSequencer  apbMasterSequencer;
 
  //Variable : ahbSlaveSequencer
  //Declaring handle to the virtual sequencer
  AhbSlaveSequencer ahbSlaveSequencer;

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
  ahbSlaveSequencer  = p_sequencer.ahbSlaveSequencer;
  ahbMasterSequencer = p_sequencer.ahbMasterSequencer;

endtask : body

`endif
