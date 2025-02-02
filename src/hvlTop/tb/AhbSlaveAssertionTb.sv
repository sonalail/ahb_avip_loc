`ifndef AHBSLAVEASSERTIONTB_INCLUDED_
`define AHBSLAVEASSERTIONTB_INCLUDED_

import AhbGlobalPackage::*;

import uvm_pkg::*;
`include "uvm_macros.svh"

module AhbSlaveAssertionTb;

  // Testbench signals (these will drive the interface signals)
  reg         hclk;
  reg         hresetn;
  reg         hreadyout;
  reg [DATA_WIDTH-1:0]  hrdata;
  reg [1:0]   hresp;
  reg [ADDR_WIDTH-1:0]  haddr;
  reg [1:0]   htrans;
  reg         hwrite;
  reg [2:0]   hsize;
  reg [2:0]   hburst;
  reg         hselx;
  reg [DATA_WIDTH-1:0]  hwdata;
  reg [3:0]   hprot;
  reg         hexokay;
  reg [3:0]   hwstrb;

  // Instantiate the interface for Slave Assertions
  AhbSlaveAssertion ahbslaveassertions_u (.hclk(hclk),
    .hresetn(hresetn),
    .hreadyout(hreadyout),
    .hrdata(hrdata),
    .hresp(hresp),
    .haddr(haddr),
    .htrans(htrans),
    .hwrite(hwrite),
    .hsize(hsize),
    .hburst(hburst),
    .hselx(hselx),
    .hwdata(hwdata),
    .hprot(hprot),
    .hexokay(hexokay),
    .hwstrb(hstrb)
  );

  // Clock generation
  always begin
    #5 hclk = ~hclk;  // 100 MHz clock (10ns period)
  end

  // Initial block to apply stimulus and reset
  initial begin
    // Initialize signals
    hclk = 0;
    hresetn = 0;
    hreadyout = 0;
    hrdata = 32'b0;
    hresp = 2'b00;
    haddr = 32'b0;
    htrans = 2'b00;
    hwrite = 1'b0;
    hsize = 3'b010;  // Word transfer
    hburst = 3'b000; // Single burst
    hselx = 1'b0;
    hwdata = 32'b0;
    hprot = 4'b0000;
    hexokay = 1'b0;
    hwstrb = 4'b1111;

    // Apply reset
    #10 hresetn = 1'b1;

    // Test 1: Valid Read Transaction
    #10;
    htrans = 2'b10;  // NONSEQ transaction
    hreadyout = 1;
    hwrite = 0;      // Read
    hrdata = 32'hA5A5A5A5;  // Read data
    haddr = 32'h0000_1000;   // Example address
    hresp = 2'b00;   // OKAY response
    #20;
    
    // Test 1.1: Invalid Read Transaction(Fail Assertion)
    #10;
    htrans = 2'b10;  // NONSEQ transaction
    hreadyout = 1;
    hwrite = 0;      // Read
    hrdata = 32'hx;  // Read data
    haddr = 32'h0000_1000;   // Example address
    hresp = 2'b00;   // OKAY response
    #20;
    

    // Test 2: Write Transaction (Pass Assertion)
    #10;
    htrans = 2'b01;  // BUSY transaction
    hreadyout = 1;
    hwrite = 1;      // Write
    hwdata = 32'hDEAD_BEEF;  // Write data
    haddr = 32'h0000_2000;   // Example address
    hresp = 2'b00;   // OKAY response
    #20;


    // Test 3: Burst Transaction (INCR)
    #10;
    htrans = 2'b10;  // NONSEQ
    hburst = 3'b001; // INCR burst
    hreadyout = 1;
    haddr = 32'h0000_3000;
    hresp = 2'b00;
    #20;

    // Test 3.1: Invalid Burst Type (Fail Assertion)
    #10;
    htrans = 2'b10;  // NONSEQ
    hburst = 3'b101; // Invalid burst type
    hreadyout = 1;
    hresp = 2'b00;
    #20;

    // Test 4: Idle State with HRESP ERROR
    #10;
    htrans = 2'b00;  // IDLE
    hreadyout = 1;
    hresp = 2'b01;   // ERROR response
    #20;
   
    // Test 4.1: Idle State with HRESP ERROR(Fail assertion)
    #10;
    htrans = 2'b00;  // IDLE
    hreadyout = 1;
    hresp = 2'b00;   // OKAY  response
    #20;
    
    //Test 5 :HSIZE matches data width
    #10;
    hreadyout = 1;
    htrans = 2'b10; //NONSEQ
    hsize = 3'b101;
    #20;
    
   //Test 5.1 :HSIZE does not matche data width)(Fail Assertion)
    #10;
    hreadyout = 1;
    htrans = 2'b10; //NONSEQ
    hsize = 3'b110;
    #20;
    
    //Test 6 :HRESP is OKAY for valid transaction (Pass assertion)
    #10;
    hreadyout = 1; // Ready signal is high
    htrans = 2'b10; // NONSEQ (valid transaction)
    hresp = 1'b0; // OKAY response
    #20;
   
    //Test 6.1 :HRESP is OKAY for valid transaction (Fail assertion)
    #10;
    hreadyout = 1; // Ready signal is high
    htrans = 2'b10; // NONSEQ (valid transaction)
    hresp = 1'b1; // ERROR response
    #20;       
     
    
    // End simulation
    $finish;
  end

  // Monitor the assertion errors
  initial begin
    $monitor("Time=%0t, htrans=%b, hresp=%b, hreadyout=%b, hrdata=%h, haddr=%h, hwrite=%b, hburst=%b",
             $time, htrans, hresp, hreadyout, hrdata, haddr, hwrite, hburst);
  end

endmodule
`endif
