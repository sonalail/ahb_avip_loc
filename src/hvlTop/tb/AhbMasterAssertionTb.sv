`ifndef AHBMASTERASSERTIONTB_INCLUDED_
`define AHBMASTERASSERTIONTB_INCLUDED_

import AhbGlobalPackage::*;

import uvm_pkg::*;
`include "uvm_macros.svh"

module AhbMasterAssertionTb;

  //-------------------------------------------------------
  // Testbench Signals
  //-------------------------------------------------------
  reg         hclk;
  reg         hresetn;
  reg [ADDR_WIDTH-1:0]  haddr;
  reg [DATA_WIDTH-1:0]  hwdata;
  reg [2:0]   hsize;
  reg [2:0]   hburst;
  reg [1:0]   htrans;
  reg         hwrite;
  reg         hready;
  reg         hresp;
  reg         hexcl;
  reg [HPROT_WIDTH-1:0]   hprot;
  reg [HMASTER_WIDTH-1:0]   hmaster;
  reg         hmastlock;
  reg         htransValid;
  reg [DATA_WIDTH-1:0]  hwdataValid;

  //-------------------------------------------------------
  // Instantiate the Assertions Interface
  //-------------------------------------------------------
  AhbMasterAssertion ahbmasterassertions_u (
    .hclk(hclk),
    .hresetn(hresetn),
    .haddr(haddr),
    .hwdata(hwdata),
    .hsize(hsize),
    .hburst(hburst),
    .htrans(htrans),
    .hwrite(hwrite),
    .hready(hready),
    .hresp(hresp),
    .hexcl(hexcl),
    .hprot(hprot),
    .hmaster(hmaster),
    .hmastlock(hmastlock),
    .htransValid(htransValid),
    .hwdataValid(hwdataValid)
  );

  //-------------------------------------------------------
  // Clock Generation
  //-------------------------------------------------------
  always begin
    #5 hclk = ~hclk;
  end

  //-------------------------------------------------------
  // Reset Generation
  //-------------------------------------------------------
  initial begin
    hclk = 0;
    hresetn = 0;
    #15 hresetn = 1;
  end

  //-------------------------------------------------------
  // Stimulus Generation
  //-------------------------------------------------------
  initial begin
    // Initializing signals
    haddr = 32'h00000000;
    hwdata = 32'h12345678;
    hsize = 3'b010;  // Word (32-bit)
    hburst = 3'b001; // INCR burst type
    htrans = 2'b10;  // Non-sequential transfer
    hwrite = 1;
    hready = 1;
    hresp = 1'b0;    // OKAY response
    hexcl = 0;
    hprot = 4'b0000;
    hmaster = 4'b0001;
    hmastlock = 0;
    htransValid = 1;
    hwdataValid = 1;

    // Stimulus 1: **Valid Write Transaction** (Passing Test for Assertions)
    #10;
    haddr = 32'h00000004;
    hwdata = 32'h87654321;
    hsize = 3'b010;  // 32-bit transfer
    htrans = 2'b11;  // Sequential transfer
    hwrite = 1;
    hready = 1;
    #20;

    // Stimulus 2: **Invalid HADDR Alignment** (Failing the HADDR Alignment Assertion)
    #10;
    haddr = 32'h00000003; // Misaligned address (not divisible by 4 for 32-bit transfer)
    hwdata = 32'hDEADBEEF;
    hwrite = 1;
    hready = 1;
    htrans = 2'b10;  // Non-sequential transfer
    #20;

    // Stimulus 3: **Valid HADDR within range**
    #10;
    haddr = 32'h10000000;  // Valid address in the range
    hsize = 3'b010;        // 32-bit transfer
    htrans = 2'b11;        // Sequential transfer
    hwrite = 1;
    hready = 1;
    #20;

    // Stimulus 4: **HADDR out of range** (Failing the Address Range Assertion)
    #10;
    haddr = 32'hFFFFFFFFF; // Invalid address out of range
    hwdata = 32'hC0FFEE;
    hsize = 3'b010;        // 32-bit transfer
    htrans = 2'b10;        // Non-sequential transfer
    hwrite = 1;
    hready = 1;
    #20;

    // Stimulus 5: **Valid HRESP** (Passing Test for HRESP OKAY Assertion)
    #10;
    haddr = 32'h00000008;
    hwdata = 32'hABCDEF01;
    hresp = 1'b0;   // OKAY response
    htrans = 2'b11; // Sequential transfer
    hready = 1;
    hwrite = 1;
    #20;

    // Stimulus 6: **Invalid HRESP** (Failing the HRESP Error Assertion)
    #10;
    hresp = 1'b1; // ERROR response
    hready = 1;
    hwrite = 1;
    htrans = 2'b11; // Sequential transfer
    #20;

    // Stimulus 7: **Burst Transfer (INCR)**
    #10;
    haddr = 32'h00000000;
    hburst = 3'b001; // INCR burst
    hsize = 3'b001;  // 8-bit transfer
    htrans = 2'b11;  // Sequential transfer
    hwrite = 1;
    hready = 1;
    #20;

    // Stimulus 8: **Burst Transfer (WRAP)**
    #10;
    haddr = 32'h00000000;
    hburst = 3'b010; // WRAP burst
    hsize = 3'b010;  // 16-bit transfer
    htrans = 2'b11;  // Sequential transfer
    hwrite = 1;
    hready = 1;
    #20;

    // Stimulus 9: **HREADY Stability Test** (Passing HREADY Stability Test)
    #10;
    hready = 0; // Simulating slave not ready
    #10;
    hready = 1; // HREADY must stay stable until slave is ready
    #20;

    // Stimulus 10: **HMASTLOCK** (Valid locked transfer)
    #10;
    hmastlock = 1;  // Assert HMASTLOCK during a transfer
    haddr = 32'h00000010;
    htrans = 2'b11; // Sequential transfer
    hwrite = 1;
    hready = 1;
    #20;

    // Stimulus 11: **Invalid INCR Burst Address**
    #10;
    haddr = 32'h00000001;  // Invalid address for INCR burst type
    hburst = 3'b001;       // INCR burst type
    hsize = 3'b001;        // 8-bit transfer
    htrans = 2'b11;        // Sequential transfer
    hwrite = 1;
    hready = 1;
    #20;

    // Stimulus 12: **Valid INCR Burst Address**
    #10;
    haddr = 32'h00000000;  // Valid address for INCR burst type
    hburst = 3'b001;       // INCR burst type
    hsize = 3'b010;        // 16-bit transfer
    htrans = 2'b11;        // Sequential transfer
    hwrite = 1;
    hready = 1;
    #20;

    // Stimulus 13: **Burst wrapping error**
    #10;
    haddr = 32'h00000010; // Address for WRAP burst type, but it doesn't align
    hburst = 3'b010;      // WRAP burst type
    hsize = 3'b001;       // 8-bit transfer
    htrans = 2'b11;       // Sequential transfer
    hwrite = 1;
    hready = 1;
    #20;

    $finish;
  end

endmodule
`endif
