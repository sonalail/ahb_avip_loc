`ifndef AHBSLAVE8BWRITEREADSEQUENCE_INCLUDED_
`define AHBSLAVE8BWRITEREADSEQUENCE_INCLUDED_     

class AhbSlave8bWriteReadSequence extends AhbSlaveBaseSequence;
  `uvm_object_utils(AhbSlave8bWriteReadSequence)

 
  extern function new(string name = "AhbSlave8bWriteReadSequence");
  extern task body();
endclass : AhbSlave8bWriteReadSequence
function AhbSlave8bWriteReadSequence::new(string name = "AhbSlave8bWriteReadSeq");
  super.new(name);
endfunction : new

 
task AhbSlave8bWriteReadSequence::body();
  req=AhbMasterTransaction::type_id::create("req");
  start_item(req);
  if(!req.randomize()) begin
    `uvm_error(get_type_name(),"randomization failed");
  end
  req.print();
  finish_item(req);
endtask : body
`endif
