`ifndef AHBENVIRONMENTCONFIG_INCLUDED_
`define AHBENVIRONMENTCONFIG_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbEnvironmentConfig
// This class is used as configuration class for AhbEnvironment and its components
//--------------------------------------------------------------------------------------------
class AhbEnvironmentConfig extends uvm_object;
  `uvm_object_utils(AhbEnvironmentConfig)
  
  //Variable: hasScoreboard
  //Enables the scoreboard. Default value is 1
  bit hasScoreboard = 1;

  //Variable: hasVirtualSequencer
  //Enables the virtual sequencer. Default value is 1
  bit hasVirtualSequencer = 1;

  //Variable: noOfSlaves
  //Number of slaves connected to the SPI interface
  int noOfSlaves;

  //Variable: ahbMasterAgentConfig
  //Handle for master agent configuration
  AhbMasterAgentConfig ahbMasterAgentConfig;

  //Variable: ahbSlaveAgentConfig
  //Dynamic array of slave agnet configuration handles
  AhbSlaveAgentConfig ahbSlaveAgentConfig[];

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
  
  printer.print_field ("hasScoreboard", hasScoreboard, $bits(has_scoreboard), UVM_DEC);
  printer.print_field ("hasVirtualSequencer", hasVirtualSequencer, $bits(has_virtual_seqr), UVM_DEC);
  printer.print_field ("noOfSlaves",  noOfSlaves,  $bits(no_of_slaves), UVM_DEC);

endfunction : do_print

`endif
