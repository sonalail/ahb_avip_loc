`ifndef AHBSLAVE64BWRITESEQUENCE_INCLUDED_
`define AHBSLAVE64BWRITESEQUENCE_INCLUDED_  

class AhbSlave64bWriteSequence extends AhbSlaveBaseSequence;
  `uvm_object_utils(AhbSlave64bWriteSequence)
  extern function new(string name="AhbSlave64bWriteSequence");
  extern task body();
endclass : AhbSlave64bWriteSequence
 
    function AhbSlave64bWriteSequence::new(string name="AhbSlave64bWriteSequence");
  super.new(name);
endfunction : new
 
task AhbSlave64bWriteSequence::body();
  req=AhbMasterTransaction::type_id::create("req");
  start_item(req);
  if(!req.randomize()) begin
    `uvm_fatal("APB","Rand failed");
  end
  req.print();
  finish_item(req);
endtask : body
`endif

