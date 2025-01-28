`ifndef AHBSLAVE8BREADSEQUENCE_INCLUDED_
`define AHBSLAVE8BREADSEQUENCE_INCLUDED_             

class AhbSlave8bReadSequence extends AhbSlaveBaseSequence;
  `uvm_object_utils(AhbSlave8bReadSequence)
  extern function new(string name="AhbSlave8bReadSequence");
  extern task body();
endclass : AhbSlave8bReadSequence
 
function AhbSlave8bReadSequence::new(string name="AhbSlave8bReadSequence");
  super.new(name);
endfunction : new

 
task AhbSlave8bReadSequence::body();
  req=AhbMasterTransaction::type_id::create("req");
  start_item(req);
  if(!req.randomize())
  begin
    `uvm_error(get_type_name(),"randomization failed");
  end
  req.print();
  finish_item(req);
endtask : body
`endif   
