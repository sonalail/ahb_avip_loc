`ifndef AHB_MASTER_SEQ_PKG_INCLUDED_
`define AHB_MASTER_SEQ_PKG_INCLUDED_

//--------------------------------------------------------------------------------------------
// Package : apb_master_seq_pkg
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
