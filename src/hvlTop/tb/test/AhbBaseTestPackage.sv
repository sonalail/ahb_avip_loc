`ifndef AHBBASETESTPKG_INCLUDED_
`define AHBBASETESTPKG_INCLUDED_

//-----------------------------------------------------------------------------------------
// Package: ahb base_test
//  Includes all the files written to run the simulation
//--------------------------------------------------------------------------------------------
package AhbBaseTestPackage;

  //-------------------------------------------------------
  // Import uvm package
  //-------------------------------------------------------
  `include "uvm_macros.svh"
  import uvm_pkg::*;

  //-------------------------------------------------------
  // Importing the required packages
  //-------------------------------------------------------
  import AhbGlobalPackage::*;
  import AhbMasterPackage::*;
  import AhbSlavePackage::*;
  import AhbEnvironmentPackage::*;
  import AhbMasterSequencePackage::*;
  import AhbSlaveSequencePackage::*;
  import AhbVirtualSequencePackage::*;
  
  //-------------------------------------------------------
  // Including the base test files
  //-------------------------------------------------------
  `include "AhbBaseTest.sv"

endpackage : AhbBaseTestPackage

`endif
