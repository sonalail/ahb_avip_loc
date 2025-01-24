`ifndef AHBVIRTUALBASESEQUENCE_INCLUDED_
`define AHBVIRTUALBASESEQUENCE_INCLUDED_

class AhbVirtualBaseSequence extends uvm_sequence; 
  `uvm_object_utils(AhbVirtualBaseSequence)
  `uvm_declare_p_sequencer(AhbVirtualSequencer)

   AhbEnvironmentConfig ahbEnvironmentConfig;

  extern function new(string name = "AhbVirtualBaseSequence");
  extern task body();

endclass : AhbVirtualBaseSequence

function AhbVirtualBaseSequence::new(string name = "AhbVirtualBaseSequence");
  super.new(name);
endfunction : new

task AhbVirtualBaseSequence::body();
	if (!uvm_config_db#(AhbEnvironmentConfig)::get(null, get_full_name(), "AhbEnvironmentConfig", ahbEnvironmentConfig )) begin
		`uvm_fatal("AHBENVIRONMENTCONFIG", "cannot get() ENV_cfg from uvm_config_db.Have you set() it?")
	end

 	if (!$cast(p_sequencer, m_sequencer)) begin
		`uvm_error(get_full_name(), "Virtual sequencer pointer cast failed")
	end
endtask : body

`endif
