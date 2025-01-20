`ifndef AHB_ENV_CONFIG_INCLUDED_
`define AHB_ENV_CONFIG_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbEnvironmentConfig
// This class is used as configuration class for AhbEnvironment and its components
//--------------------------------------------------------------------------------------------
class AhbEnvironmentConfig extends uvm_object;
  `uvm_object_utils(AhbEnvironmentConfig)
  
  //Variable: has_scoreboard
  //Enables the scoreboard. Default value is 1
  bit has_scoreboard = 1;

  //Variable: has_virtual_sqr
  //Enables the virtual sequencer. Default value is 1
  bit has_virtual_seqr = 1;

  //Variable: no_of_slaves
  //Number of slaves connected to the SPI interface
  int no_of_slaves;

  //Variable: master_agent_cfg_h
  //Handle for master agent configuration
  AhbMasterAgentConfig ahb_master_agent_cfg_h;

  //Variable: slave_agent_cfg_h
  //Dynamic array of slave agnet configuration handles
  AhbSlaveAgentConfig ahb_slave_agent_cfg_h[];

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbEnvironmentConfig");
  extern function void do_print(uvm_printer printer);

endclass : AhbEnvironmentConfig

//--------------------------------------------------------------------------------------------
// Construct: new
//  Initialization of new memory
//
// Parameters:
//  name - AhbEnvironmentConfig
//--------------------------------------------------------------------------------------------
function  AhbEnvironmentConfig::new(string name = "AhbEnvironmentConfig");
  super.new(name);
endfunction : new

//--------------------------------------------------------------------------------------------
// Function: do_print method
//  Print method can be added to display the data members values
//
// Parameters :
//  printer - uvm_printer
//--------------------------------------------------------------------------------------------
function void AhbEnvironmentConfig::do_print(uvm_printer printer);
  super.do_print(printer);
  
  printer.print_field ("has_scoreboard",   has_scoreboard,   $bits(has_scoreboard),   UVM_DEC);
  printer.print_field ("has_virtual_seqr", has_virtual_seqr, $bits(has_virtual_seqr), UVM_DEC);
  printer.print_field ("no_of_slaves",     no_of_slaves,     $bits(no_of_slaves),     UVM_DEC);

endfunction : do_print

`endif
