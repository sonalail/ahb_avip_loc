`ifndef AHB_VIRTUAL_BASE_SEQ_INCLUDED_
`define AHB_VIRTUAL_BASE_SEQ_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbVirtualBaseSequence
// Holds the handle of actual sequencer.
//--------------------------------------------------------------------------------------------
class AhbVirtualBaseSequence extends uvm_sequence;
  `uvm_object_utils(AhbVirtualBaseSequence)
  
  //Declaring p_sequencer
  `uvm_declare_p_sequencer(ApbVirtualSequencer)
  
  //Variable : ahb_master_seqr_h
  //Declaring handle to the virtual sequencer
  ApbMasterSequencer ahb_master_seqr_h;

  //Variable : ahb_master_seqr_h
  //Declaring handle to the virtual sequencer
  ApbSlaveSequencer ahb_slave_seqr_h;

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
  ahb_slave_seqr_h  = p_sequencer.ahb_slave_seqr_h;
  ahb_master_seqr_h = p_sequencer.ahb_master_seqr_h;

endtask : body

`endif

