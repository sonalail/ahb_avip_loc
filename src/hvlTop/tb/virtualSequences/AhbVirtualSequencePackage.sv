`ifndef AHBVIRTUALSEQUENCEPACKAGE_INCLUDED_
`define AHBVIRTUALSEQUENCEPACKAGE_INCLUDED_

//--------------------------------------------------------------------------------------------
// Package : AhbVirtualSequencePackage
//  Includes all the master seq files declared
//--------------------------------------------------------------------------------------------
package AhbVirtualSequencePackage;

  //-------------------------------------------------------
  // Importing UVM Pkg
  //-------------------------------------------------------
  `include "uvm_macros.svh"
  import AhbGlobalPackage::*;
  import AhbMasterPackage::*;
  import AhbSlavePackage::*;
  import AhbEnvironmentPackage::*;
  import AhbMasterSequencePackage::*;
  import AhbSlaveSequencePackage::*;
  import AhbVirtualSequencePackage::*;

  //-------------------------------------------------------
  // Including required seq files
  //-------------------------------------------------------
  `include "AhbVirtualBaseSequence.sv"
  
endpackage : AhbVirtualSequencePackage

`endif
