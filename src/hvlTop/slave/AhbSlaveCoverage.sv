`ifndef AHBSLAVECOVERAGE_INCLUDED_
`define AHBSLAVECOVERAGE_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: AhbMasterCoverage
// This class is used to include covergroups and bins required for functional coverage
//--------------------------------------------------------------------------------------------
class AhbMasterCoverage extends uvm_subscriber #(AhbSlaveTranscation);
  `uvm_component_utils(AhbSlaveCoverage)
 
  //Variable: ahb_slave_agent_cfg_h
  //Declaring handle for slave agent configuration class 
  AhbSlaveAgentConfig apbSlaveAgentConfig;
  
  //-------------------------------------------------------
  Covergroup: ahbSlaveCovergroup
  
  endgroup: ahbSlaveCovergroup

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "AhbSlaveCoverage", uvm_component parent = null);
  extern function void write(AhbSlaveTranscation t);
  extern virtual function void report_phase(uvm_phase phase);

endclass : AhbSlaveCoverage

//--------------------------------------------------------------------------------------------
// Construct: new
//  Initializes memory for new object
//
// Parameters:
//  name - ahbSlaveCoverage
//  parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function  AhbSlaveCoverage::new(string name = "AhbSlaveCoverage", uvm_component parent = null);
  super.new(name, parent);
  ahbSlaveCovergroup = new();
endfunction : new

//-------------------------------------------------------------------------------------------
// Function: write
// Overriding the write method declared in the parent class
//
// Parameters:
//  t - ahb_slave_tx
//--------------------------------------------------------------------------------------------
function void AhbMasterCoverage::write(AhbSlaveTransaction t);
endfunction : write

//--------------------------------------------------------------------------------------------
// Function: report_phase
// Used for reporting the coverage instance percentage values
//--------------------------------------------------------------------------------------------
function void AhbSlaveCoverage::report_phase(uvm_phase phase);
  `uvm_info(get_type_name(), $sformatf("Entered the report_phase of AHB Slave Coverage"), UVM_NONE);
  `uvm_info(get_type_name(), $sformatf("APB Slave Agent Coverage = %0.2f %%", apbSlaveCovergroup.get_coverage()), UVM_NONE);
endfunction: report_phase

`endif
