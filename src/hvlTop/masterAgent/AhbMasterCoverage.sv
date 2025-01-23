`ifndef AHBMASTERCOVERAGE_INCLUDED_
`define AHBMASTERCOVERAGE_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbMasterCoverage
// This class is used to include covergroups and bins required for functional coverage
//--------------------------------------------------------------------------------------------
class AhbMasterCoverage extends uvm_subscriber #(AhbMasterTransaction);
  `uvm_component_utils(AhbMasterCoverage)

  //Variable: apbMasterAgentConfig
  //Declaring handle for master agent configuration class
  AhbMasterAgentConfig apbMasterAgentConfig;

  //-------------------------------------------------------
  covergroup ahbMasterCovergroup;

  endgroup: ahbMasterCovergroup

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbMasterCoverage", uvm_component parent = null);
  extern function void write(AhbMasterTransaction t);
  extern virtual function void report_phase(uvm_phase phase);

endclass : AhbMasterCoverage

//--------------------------------------------------------------------------------------------
// Construct: new
//  Initializes memory for new object
//
// Parameters:
//  name - AhbMasterCoverage
//  parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function  AhbMasterCoverage::new(string name = "AhbMasterCoverage", uvm_component parent = null);
  super.new(name, parent);
  ahbMasterCovergroup = new();
endfunction : new

//-------------------------------------------------------------------------------------------
// Function: write
// Overriding the write method declared in the parent class
//
// Parameters:
//  t - AhbMasterTransaction
//--------------------------------------------------------------------------------------------
function void AhbMasterCoverage::write(AhbMasterTransaction t);

endfunction : write

//--------------------------------------------------------------------------------------------
// Function: report_phase
// Used for reporting the coverage instance percentage values
//--------------------------------------------------------------------------------------------
function void AhbMasterCoverage::report_phase(uvm_phase phase);
  `uvm_info(get_type_name(), $sformatf("Entered the report_phase of AHB Master Coverage"), UVM_NONE);
  //`uvm_info(get_type_name(), $sformatf("AHB Master Agent Coverage = %0.2f %%", ahbMasterCovergroup.get_coverage()), UVM_NONE);
endfunction: report_phase

`endif

