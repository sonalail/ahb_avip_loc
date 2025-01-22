`ifndef AHBSLAVESEQUENCEPACKAGE_INCLUDED_
`define AHBSLAVESEQUENCEPACKAGE_INCLUDED_

//--------------------------------------------------------------------------------------------
// Package : AhbSlaveSequencePackage
//  Includes all the master seq files declared
//--------------------------------------------------------------------------------------------
package AhbSlaveSequencePackage;

  //-------------------------------------------------------
  // Importing UVM Pkg and including globall and slave packages
  //-------------------------------------------------------
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import AhbGlobalPackage::*;
  import AhbSlavePackage::*;

  //-------------------------------------------------------
  // Including required ahb slave seq files
  //-------------------------------------------------------
  `include "AhbSlaveBaseSequence.sv"

endpackage : AhbSlaveSequencePackage

`endif

