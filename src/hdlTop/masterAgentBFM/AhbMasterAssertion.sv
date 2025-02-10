`ifndef AHBMASTERASSERTION_INCLUDED_
`define AHBMASTERASSERTION_INCLUDED_

//-------------------------------------------------------
// Importing Global Package
//-------------------------------------------------------
import AhbGlobalPackage::*;

//-------------------------------------------------------
// Interface: AhbMasterAssertions
//-------------------------------------------------------
interface AhbMasterAssertion (
  input        hclk,          // Clock signal
  input        hresetn,       // Active-low reset
  input [ADDR_WIDTH-1:0] haddr,         // Address bus (32 bits)
  input [DATA_WIDTH-1:0] hwdata,        // Write data bus (32 bits)
  input [2:0]  hsize,         // Size of the transfer (byte, half-word, word, etc.)
  input [2:0]  hburst,        // Burst type (SINGLE, INCR, WRAP, etc.)
  input [1:0]  htrans,        // Transaction type (IDLE, BUSY, NONSEQ, SEQ)
  input        hwrite,        // Write signal (1 for write, 0 for read)
  input        hready,        // Ready signal (indicates whether the transfer is complete)
  input        hresp,         // Response from slave (OKAY or ERROR)
  input        hexcl,         // Exclusive access signal
  input [HPROT_WIDTH-1:0]  hprot,         // Protection type (User/Supervisor, etc.)
  input [HMASTER_WIDTH -1:0]  hmaster,       // Master identifier (if multiple masters)
  input        hmastlock,     // Master lock signal
  input        htransValid,  // Signal indicating valid transaction
  input [DATA_WIDTH-1:0] hwdataValid   // Write data valid signal
);

//-------------------------------------------------------
// Importing Uvm Package
//-------------------------------------------------------
  import uvm_pkg::*;
  `include "uvm_macros.svh";

  initial begin
    `uvm_info("MASTER_ASSERTIONS","MASTER_ASSERTIONS",UVM_LOW);
  end

//-------------------------------------------------------
// Assertion Properties
//-------------------------------------------------------

// Check that HWDATA is valid when HWRITE is HIGH
property checkHwdataValid;
  @(posedge hclk) disable iff (!hresetn)
  (hwrite && hready && (htrans != 2'b00)) |-> (!$isunknown(hwdata));
endproperty
assert property (checkHwdataValid)
    $info("HWDATA is Valid When HWRITE IS HIGH");
  else $error("HWDATA contains X when HWRITE is asserted!");

// Ensure valid HTRANS values (NONSEQ or SEQ) occur only with HREADY
property checkHtransValidity;
  @(posedge hclk) disable iff (!hresetn)
  (htrans == 2'b10 || htrans == 2'b11) |-> hready;
endproperty
assert property (checkHtransValidity)
    $info("HTRANS is Valid ");
  else $error("HTRANS has an invalid value or transition!");

// Ensure HADDR is aligned based on HSIZE
property checkHaddrAlignment;
  @(posedge hclk) disable iff (!hresetn)
  (hready && (htrans != 2'b00)) |-> 
  ((hsize == 3'b001) && (haddr[0] == 1'b0)) ||
  ((hsize == 3'b010) && (haddr[1:0] == 2'b00));
endproperty
assert property (checkHaddrAlignment)
     $info("HADDR is aligned based on HSIZE"); 
else $error("HADDR is not aligned based on HSIZE!");

//Check if HADDR is within the valid range
property ifHaddrValidAndWithinRange;
  @(posedge hclk) disable iff (!hresetn)
  (hready && (htrans != 2'b00)) |-> ((haddr >= AHB_ADDR_MIN) && (haddr <= AHB_ADDR_MAX));
endproperty
assert property (ifHaddrValidAndWithinRange)
       $info("HADDR is within the valid range");
  else $error("HADDR is not within the valid range!");

// Ensure HRESP is OKAY (0) during successful transfers
property checkHrespOkay;
  @(posedge hclk) disable iff (!hresetn)
  (hready && (htrans != 2'b00)) |-> (hresp == 1'b0);
endproperty
assert property (checkHrespOkay)
       $info("HRESP is OKAY during a successful transfer");
  else $error("HRESP is not OKAY for a successful transfer!");

// Ensure HRESP is ERROR (1) during error conditions
property checkHrespErrorFixed;
  @(posedge hclk) disable iff (!hresetn)
  (hready && hresp) |-> (htrans != 2'b00);
endproperty
assert property (checkHrespErrorFixed)
       $info("HRESP is ERROR during error conditions");
  else $error("Unexpected HRESP ERROR when transfer is IDLE!");

// Ensure HREADY remains stable during wait states
property checkHreadyStability;
  @(posedge hclk) disable iff (!hresetn)
  (hready) |=> hready;
endproperty
assert property (checkHreadyStability)
       $info("HREADY remains stable during wait states");
  else $error("HREADY unexpectedly changed when slave was not ready!");

// Ensure HMASTLOCK is asserted correctly during locked transfers
property checkHmastlockCheck;
  @(posedge hclk) disable iff (!hresetn)
  (hready && htrans != 2'b00 && hmastlock) |-> (hmastlock == 1);
endproperty
assert property (checkHmastlockCheck)
       $info("HMASTLOCK is asserted during a locked transfer");
  else $error("HMASTLOCK is not asserted during a locked transfer!");

// Burst type: Check for INCR (incrementing burst)
property checkBurstIncr;
  @(posedge hclk) disable iff (!hresetn)
  (hburst == 3'b001 && htrans == 2'b11) |-> 
  (haddr == $past(haddr) + (1 << hsize));
endproperty
assert property (checkBurstIncr)
       $info("INCR burst type passed: Address incremented correctly");
  else $error("INCR burst type failed: Address not incremented correctly!");

// Burst type: Check for WRAP (wrapping burst)
property checkBurstWrap;
  @(posedge hclk) disable iff (!hresetn)
  (hburst == 3'b010 && htrans == 2'b11) |-> 
  (((haddr & ((1 << hsize) - 1)) == 0) || 
  (haddr == $past(haddr) + (1 << hsize)));
endproperty
assert property (checkBurstWrap)
       $info("WRAP burst type passed: Address wrapping is done correctly");
  else $error("WRAP burst type failed: Address wrapping incorrect!");
  

// Check for transition from BUSY to SEQ
property checkTransBusyToSeq;
  @(posedge hclk) disable iff(!hresetn)
  (htrans == 2'b01 && hready == 0 && hburst inside{[3'b010:3'b111]}) ##1
  (htrans == 2'b11 && $stable(hready) && $stable(hburst) && $stable(haddr));
endproperty
assert property(checkTransBusyToSeq)
    $info("Transition from BUSY to SEQ passed");
  else $error("Transition from BUSY to SEQ failed: Conditions not met!");


//Check for transition from BUSY to NON-SEQ
property checkTransBusyToNonSeq;
  @(posedge hclk) disable iff(!hresetn) 
  (htrans == 2'b01 && hready ==0 && hburst inside {[3'b000:3'b001]}) |=>
(htrans == 2'b10 && $stable(hready) && $stable(hburst) && $stable(haddr));
endproperty

assert property(checkTransBusyToNonSeq)
   $info("Transition from BUSY to NON - SEQ passed");
 else $error("Transition from BUSY to NON - SEQ failed: Conditions not met!");

//Check for transtion from IDLE to NON SEQ
property checkTransIdleToNonSeq;
  @(posedge hclk) disable iff(!hresetn)
     (htrans == 2'b00 && hready == 0 )|=>
  (htrans == 2'b10 && $stable(hready));
endproperty

assert property(checkTransIdleToNonSeq)
  $info("Transition from IDLE to NON-SEQ passed");
else $error("Transition from IDLE to NON-SEQ failed: Conditions not met!"); 



//stability
property checkAddrStability;
  @(posedge hclk) disable iff (!hresetn)
  (htrans == 2'b10||htrans ==2'b11) |=> $stable(haddr) throughout hready==0;
endproperty

assert property (checkAddrStability)
       $info("Address stability during waited transfer verified.");
  else $error("Address changed before HREADY HIGH!");

endinterface : AhbMasterAssertion

`endif
