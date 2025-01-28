`ifndef AHBSLAVE16BWRITESEQUENCE_INCLUDED_
`define AHBSLAVE16BWRITESEQUENCE_INCLUDED_   

class AhbSlave16bWriteSequence extends AhbSlaveBaseSequence;
  `uvm_object_utils(AhbSlave16bWriteSequence)
  extern function new(string name="AhbSlave16bWriteSequence");
  extern task body();
endclass : AhbSlave16bWriteSequence
 
function AhbSlave16bWriteSequence::new(string name="AhbSlave16bWriteSequence");
  super.new(name);
endfunction : new

 
task AhbSlave16bWriteSequence::body();
  `uvm_info(get_type_name(),$sformatf("AhbSlave16bWriteSequence"),UVM_LOW);
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

