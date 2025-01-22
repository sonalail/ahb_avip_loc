`ifndef AHBMASTERSEQUENCEPACKAGE_INCLUDED_
`define AHBMASTERSEQUENCEPACKAGE_INCLUDED_

//--------------------------------------------------------------------------------------------
// Package : AhbMasterSequencePackage
//  Includes all the master seq files declared
//--------------------------------------------------------------------------------------------
package AhbMasterSequencePackage;

  //-------------------------------------------------------
  // Importing UVM Pkg and including globall and master packages
  //-------------------------------------------------------
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import AhbGlobalPackage::*;
  import AhbMasterPackage::*;

  //-------------------------------------------------------
  // Including required ahb master seq files
  //-------------------------------------------------------
  `include "AhbMasterBaseSequence.sv"

endpackage : AhbMasterSequencePackage

`endif
