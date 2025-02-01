
`ifndef AHBSLAVEASSERTION_INCLUDED_
`define AHBSLAVEASSERTION_INCLUDED_

//-------------------------------------------------------
// Importing Global Package
//-------------------------------------------------------
import AhbGlobalPackage::*;

//-------------------------------------------------------
// Interface: ahb_slave_assertions
//-------------------------------------------------------
interface AhbSlaveAssertion (
  input        hclk,          // Clock signal
  input        hresetn,       // Active-low reset signal
  input        hreadyout,     // Slave ready output
  input [DATA_WIDTH-1:0] hrdata,        // Read data bus (32 bits)
  input   hresp,         // Response from slave (OKAY, ERROR)
  input [ADDR_WIDTH-1:0] haddr,         // Address bus (32 bits)
  input [1:0]  htrans,        // Transaction type (IDLE, BUSY, NONSEQ, SEQ)
  input        hwrite,        // Write signal (1 for write, 0 for read)
  input [2:0]  hsize,         // Transfer size (byte, half-word, word, etc.)
  input [2:0]  hburst,        // Burst type (SINGLE, INCR, WRAP, etc.)
  input        hselx,         // Slave select signal
  input [31:0] hwdata,        // Write data bus (32 bits)
  input [3:0]  hprot,         // Protection type (User/Supervisor, etc.)
  input        hexokay,       // Exclusive access response
  input [3:0]  hwstrb          // Byte-enable signals (4 bits)
);

//-------------------------------------------------------
// Assertion Properties
//-------------------------------------------------------

// Check that HREADYOUT is high during valid states
property checkHreadyoutValid;
  @(posedge hclk) disable iff (!hresetn)
  hreadyout;  // Ensure hreadyout is high during all non-IDLE states
endproperty
assert property (checkHreadyoutValid)
       $info("HREADYOUT is high during valid transactions!");
  else $error("HREADYOUT is not high during valid transactions!");

// Check that HRESP is ERROR for invalid transfers (htrans == IDLE)
property checkHrespErrorOnInvalid;
  @(posedge hclk) disable iff (!hresetn)
  (hreadyout && (htrans == 2'b00)) |-> (hresp == 1'b1);  // ERROR response for IDLE state
endproperty
assert property (checkHrespErrorOnInvalid)
       $info("HRESP is ERROR for valid transfers!");
  else $error("HRESP is not ERROR for invalid transfers!");

// Check that HRESP is OKAY for valid transactions (htrans != IDLE)
property checkHrespOkayForValid;
  @(posedge hclk) disable iff (!hresetn)
  (hreadyout && (htrans != 2'b00)) |-> (hresp == 1'b0);  // OKAY response for valid transactions
endproperty
assert property (checkHrespOkayForValid)
       $info("HRESP is OKAY for valid transactions!");
  else $error("HRESP is not OKAY for valid transactions!");

// Check slave responds with correct HRDATA during read transfers
property checkSlaveHrdataValid;
  @(posedge hclk) disable iff (!hresetn)
  (!hwrite && hreadyout && (htrans != 2'b00)) |-> (!$isunknown(hrdata));  // HRDATA must be valid during read transfers
endproperty
assert property (checkSlaveHrdataValid)
       $info("HRDATA is valid during read transfer!");
  else $error("HRDATA is invalid during read transfer!");

// Check slave does not alter HADDR during transfer
property checkHaddrUnchanged;
  @(posedge hclk) disable iff (!hresetn)
  (hreadyout && (htrans != 2'b00)) |-> (haddr == $past(haddr));  // Ensure HADDR is unchanged during transfer
endproperty
assert property (checkHaddrUnchanged)
       $info("HADDR remains unchanged during a transfer!");
  else $error("HADDR changed unexpectedly during a transfer!");

// Check that HSIZE matches the data width
property checkHsizeMatchesData;
  @(posedge hclk) disable iff (!hresetn)
  (hreadyout && (htrans != 2'b00)) |-> ((1 << hsize) <= 32);  // Ensure size is valid
endproperty
assert property (checkHsizeMatchesData)
       $info("HSIZE matches the data width supported by the slave!");
  else $error("HSIZE does not match the data width supported by the slave!");

// Check burst type compliance (ensure only valid burst types are used for each transaction)
property checkBurstTypeValid;
  @(posedge hclk) disable iff (!hresetn)
  (hreadyout && (htrans != 2'b00)) |-> (hburst == 3'b000 || hburst == 3'b001 || hburst == 3'b010 || hburst == 3'b011 || hburst == 3'b100);  // Valid burst types
endproperty
assert property (checkBurstTypeValid)
       $info("Valid burst type!");
  else $error("Invalid burst type detected!");

endinterface : AhbSlaveAssertion

`endif

