 
`ifndef AHBMASTERPACKAGE_INCLUDED_
`define AHBMASTERPACKAGE_INCLUDED_

//--------------------------------------------------------------------------------------------
// Package: AhbMasterPackage
//  Includes all the files related to AhbMaster
//--------------------------------------------------------------------------------------------
package AhbMasterPackage;

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
  `include "AhbMasterAgentConfig.sv"
  `include "AhbMasterTransaction.sv"
  `include "AhbMasterSequenceItemConverter.sv"
  `include "AhbMasterConfigConverter.sv"
  `include "AhbMasterSequencer.sv"
  `include "AhbMasterDriverProxy.sv"
  `include "AhbMasterMonitorProxy.sv"
  `include "AhbMasterCoverage.sv"
  `include "AhbMasterAgent.sv"
  
endpackage : AhbMasterPackage

`endif




