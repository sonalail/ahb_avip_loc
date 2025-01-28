`ifndef AHBSLAVE32BWRITESEQUENCE_INCLUDED_
`define AHBSLAVE32BWRITESEQUENCE_INCLUDED_  

class AhbSlave32bWriteSequence extends AhbSlaveBaseSequence;
  `uvm_object_utils(AhbSlave32bWriteSequence)
  extern function new(string name="AhbSlave32bWriteSequence");
  extern task body();
endclass : AhbSlave32bWriteSequence
 
function AhbSlave32bWriteSequence::new(string name="AhbSlave32bWriteSequence");
  super.new(name);
endfunction : new
 
task AhbSlave32bWriteSequence::body();
  req=AhbMasterTransaction::type_id::create("req");
  start_item(req);
  if(!req.randomize()) begin
    `uvm_fatal("APB","Rand failed");
  end
  req.print();
  finish_item(req);
endtask : body
`endif

