`ifndef AHB_SLAVE_PKG_INCLUDED_
`define AHB_SLAVE_PKG_INCLUDED_

//--------------------------------------------------------------------------------------------
// Package: ahb_slave_pkg
//  Includes all the files related to ahb_slave
//--------------------------------------------------------------------------------------------
package AhbSlavePackage;

  //-------------------------------------------------------
  // Import uvm package
  //-------------------------------------------------------
  `include "uvm_macros.svh"
  import uvm_pkg::*;

  //-------------------------------------------------------
  // Import ahb_global_pkg 
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
  
endpackage : ahb_slave_pkg

`endif
