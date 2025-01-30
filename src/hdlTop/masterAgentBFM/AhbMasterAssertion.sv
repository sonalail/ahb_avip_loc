`ifndef AHBMASTERASSERTIONS_INCLUDED_
`define AHBMASTERASSERTIONS_INCLUDED_

//-------------------------------------------------------
// Importing Global Package
//-------------------------------------------------------
import AhbGlobalPackage::*;

//-------------------------------------------------------
// Interface: AhbMasterAssertions
//-------------------------------------------------------
interface AhbMasterAssertions (
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
  input        htrans_valid,  // Signal indicating valid transaction
  input [DATA_WIDTH-1:0] hwdata_valid   // Write data valid signal
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
  else $error("HWDATA contains X when HWRITE is asserted!");

// Ensure valid HTRANS values (NONSEQ or SEQ) occur only with HREADY
property checkHtransValidity;
  @(posedge hclk) disable iff (!hresetn)
  (htrans == 2'b10 || htrans == 2'b11) |-> hready;
endproperty
assert property (checkHtransValidity)
  else $error("HTRANS has an invalid value or transition!");

// Ensure HADDR is aligned based on HSIZE
property checkHaddrAlignment;
  @(posedge hclk) disable iff (!hresetn)
  (hready && (htrans != 2'b00)) |-> 
  ((hsize == 3'b001) |-> (haddr[0] == 1'b0)) &&
  ((hsize == 3'b010) |-> (haddr[1:0] == 2'b00));
endproperty
assert property (checkHaddrAlignment)
  else $error("HADDR is not aligned based on HSIZE!");

// Check if HADDR is within the valid range
property ifHaddrValidAndWithinRange;
  @(posedge hclk) disable iff (!hresetn)
  (hready && (htrans != 2'b00)) |-> ((haddr >= AHB_ADDR_MIN) && (haddr <= AHB_ADDR_MAX));
endproperty
assert property (ifHaddrValidAndWithinRange)
  else $error("HADDR is not within the valid range!");

// Ensure HRESP is OKAY (0) during successful transfers
property checkHrespOkay;
  @(posedge hclk) disable iff (!hresetn)
  (hready && (htrans != 2'b00)) |-> (hresp == 1'b0);
endproperty
assert property (checkHrespOkay)
  else $error("HRESP is not OKAY for a successful transfer!");

// Ensure HRESP is ERROR (1) during error conditions
property checkHrespErrorFixed;
  @(posedge hclk) disable iff (!hresetn)
  (hready && hresp) |-> (htrans != 2'b00);
endproperty
assert property (checkHrespErrorFixed)
  else $error("Unexpected HRESP ERROR when transfer is IDLE!");

// Ensure HREADY remains stable during wait states
property checkHreadyStability;
  @(posedge hclk) disable iff (!hresetn)
  (!hready) |-> ##1 !hready;
endproperty
assert property (checkHreadyStability)
  else $error("HREADY unexpectedly changed when slave was not ready!");

// Ensure HMASTLOCK is asserted correctly during locked transfers
property checkHmastlockCheck;
  @(posedge hclk) disable iff (!hresetn)
  (hready && htrans != 2'b00 && hmastlock) |-> (hmastlock == 1);
endproperty
assert property (checkHmastlockCheck)
  else $error("HMASTLOCK is not asserted during a locked transfer!");

// Burst type: Check for INCR (incrementing burst)
property checkBurstIncr;
  @(posedge hclk) disable iff (!hresetn)
  (hburst == 3'b001 && htrans == 2'b11) |-> 
  (haddr == $past(haddr) + (1 << hsize));
endproperty
assert property (checkBurstIncr)
  else $error("INCR burst type failed: Address not incremented correctly!");

// Burst type: Check for WRAP (wrapping burst)
property checkBurstWrap;
  @(posedge hclk) disable iff (!hresetn)
  (hburst == 3'b010 && htrans == 2'b11) |-> 
  (((haddr & ((1 << hsize) - 1)) == 0) || 
  (haddr == $past(haddr) + (1 << hsize)));
endproperty
assert property (checkBurstWrap)
  else $error("WRAP burst type failed: Address wrapping incorrect!");

endinterface : AhbMasterAssertions

`endif
