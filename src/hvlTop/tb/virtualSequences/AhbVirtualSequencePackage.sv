`ifndef AHBVIRTUALSEQUENCEPACKAGE_INCLUDED_
`define AHBVIRTUALSEQUENCEPACKAGE_INCLUDED_

package AhbVirtualSequencePackage;

  `include "uvm_macros.svh"
  import uvm_pkg::*;
  import AhbGlobalPackage::*;
  import AhbMasterPackage::*;
  import AhbSlavePackage::*;
  import AhbMasterSequencePackage::*;
  import AhbSlaveSequencePackage::*;
  import AhbEnvironmentPackage::*;

  `include "AhbVirtualBaseSequence.sv"
  
endpackage : AhbVirtualSequencePackage

`endif
