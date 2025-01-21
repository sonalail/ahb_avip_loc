`ifndef AHBSLAVEPACKAGE_INCLUDED_
`define AHBSLAVEPACKAGE_INCLUDED_

//--------------------------------------------------------------------------------------------
// Package: AhbSlavePackage
//  Includes all the files related to ahb_slave
//--------------------------------------------------------------------------------------------
package AhbSlavePackage;

  //-------------------------------------------------------
  // Import uvm package
  //-------------------------------------------------------
  `include "uvm_macros.svh"
  import uvm_pkg::*;

  //-------------------------------------------------------
  // Import AhbGlobalPackage 
  //-------------------------------------------------------
  import AhbGlobalPackage::*;

  //-------------------------------------------------------
  // Include all other files
  //-------------------------------------------------------
  `include "AhbSlaveAgentConfig.sv"
  `include "AhbSlaveTransaction.sv"
  `include "AhbSlaveSequenceItemConverter.sv"
  `include "AhbSlaveConfigConverter.sv"
  `include "AhbSlaveSequencer.sv"
  `include "AhbSlaveDriverProxy.sv"
  `include "AhbSlaveMonitorProxy.sv"
  `include "AhbSlaveCoverage.sv"
  `include "AhbSlaveAgent.sv"
  
endpackage : AhbSlavePackage

`endif
