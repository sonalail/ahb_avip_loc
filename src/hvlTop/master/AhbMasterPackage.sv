 
`ifndef AHB_MASTER_PKG_INCLUDED_
`define AHB_MASTER_PKG_INCLUDED_

//--------------------------------------------------------------------------------------------
// Package: ahb_master_pkg
//  Includes all the files related to ahb_master
//--------------------------------------------------------------------------------------------
package AhbMasterPackage;

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
  `include "AhbMasterAgentConfig.sv"
  `include "AhbMasterTransaction.sv"
  `include "AhbMasterSequenceItemConverter.sv"
  `include "AhbMasterConfigConverter.sv"
  `include "AhbMasterSequencer.sv"
  `include "AhbMasterDriverProxy.sv"
  `include "AhbMasterMonitorProxy.sv"
  `include "AhbMasterCoverage.sv"
  `include "AhbMasterAgent.sv"
  
endpackage : ahb_master_pkg

`endif




