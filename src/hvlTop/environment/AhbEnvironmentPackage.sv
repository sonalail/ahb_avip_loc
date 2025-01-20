`ifndef_ENV_PKG_INCLUDED_
`define ahb_ENV_PKG_INCLUDED_

//--------------------------------------------------------------------------------------------
// Package: ahb_env_pkg
// Includes all the files related to ahb env
//--------------------------------------------------------------------------------------------
package AhbEnvironmentPackage;
  
  //-------------------------------------------------------
  // Importing uvm packages
  //-------------------------------------------------------
  `include "uvm_macros.svh"
  import uvm_pkg::*;

  //-------------------------------------------------------
  // Importing the required packages
  //-------------------------------------------------------
  import AhbGlobalPackage::*;
  import AhbMasterPackage::*;
  import AhbSlavePackage::*;

  //-------------------------------------------------------
  // Including the required files
  //-------------------------------------------------------
  `include "AhbEnvironmentConfig.sv"
  `include "AhbVirtualSequencer.sv"
  `include "AhbScoreboard.sv"
  `include "AhbEnvironment.sv"

endpackage : AhbEnvironmentPackage

`endif
